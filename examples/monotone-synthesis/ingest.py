"""Continuous ingest: the monotone synthesis loop as a resumable process.

Each invocation loads the persisted state, applies one batch of new events (offers and
retirement requests, e.g. the receipts of one commit), checks the spec on the result, and
replaces the state file atomically. Nothing already admitted is revisited; a pending
candidate is retried exactly when its last missing premise lands, in this batch or a later
one. Re-ingesting a batch already applied changes nothing (events are keyed).

Spec checked after every batch (refuses to write state otherwise):
  reach = least closure of the log's live rules from scratch
  reach = closure of every verified candidate offered so far (saturated)
  reach of the previous state is contained in reach (monotone)

The admission rules are MonotoneSynthesis.lean's (add: verified, fresh, premises reachable;
retire: both live, same head, replacement's premises reachable without the retired one).
This is a second implementation, written apart from loop.py; gate.py checks they agree.

usage: ingest.py STATE EVENTS.jsonl [--batch COMMIT]   (no --batch: every batch in order)
       ingest.py STATE --summary
"""
import argparse, hashlib, json, os, sys
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("state")
ap.add_argument("events", nargs="?")
ap.add_argument("--batch", default="")
ap.add_argument("--summary", action="store_true")
args = ap.parse_args()

def key(ev):
    a = ev["art"]
    n = ev.get("new")
    return f'{ev["kind"]}:{a["id"]}:{n["id"] if n else "-"}'

def verified(a):
    return a["verdict"] == "PASSED" and a["observed"] in ("root", "reached")

def fresh_state():
    return {"log": [], "arts": {}, "live": [], "pending": {}, "retire_waits": {},
            "pool": {}, "seen": [], "batches": [], "ops": {}, "reach": []}

def load():
    if os.path.exists(args.state):
        return json.load(open(args.state))
    return fresh_state()

def save(st):
    tmp = args.state + ".tmp"
    with open(tmp, "w") as f:
        json.dump(st, f, sort_keys=True)
    os.replace(tmp, args.state)

def closure(rules):
    have, cnt, wait, q = set(), {}, defaultdict(list), []
    for i, (h, ps) in rules.items():
        m = [p for p in set(ps) if p not in have]
        cnt[i] = len(m)
        for p in m:
            wait[p].append(i)
        if not m:
            q.append(i)
    while q:
        i = q.pop()
        h = rules[i][0]
        if h in have:
            continue
        have.add(h)
        for j in wait.pop(h, ()):
            cnt[j] -= 1
            if cnt[j] == 0:
                q.append(j)
    return have

class Engine:
    def __init__(self, st):
        self.st = st
        self.arts = {int(k): v for k, v in st["arts"].items()}
        self.live = set(st["live"])
        self.provides = defaultdict(set)
        for i in self.live:
            self.provides[self.arts[i]["head"]].add(i)
        self.pending = {int(k): set(v) for k, v in st["pending"].items()}
        self.waiters = defaultdict(set)
        for i, miss in self.pending.items():
            for p in miss:
                self.waiters[p].add(i)
        self.retire_waits = defaultdict(list, {int(k): v for k, v in st["retire_waits"].items()})
        self.used = {e[1] for e in st["log"] if e[0] == "add"}
        self.ops = defaultdict(int, st["ops"])

    def reach(self):
        return {h for h, s in self.provides.items() if s}

    def admit(self, a):
        got, stack = [], [a]
        while stack:
            x = stack.pop()
            new = not self.provides[x["head"]]
            self.st["log"].append(["add", x["id"]])
            self.live.add(x["id"]); self.used.add(x["id"])
            self.provides[x["head"]].add(x["id"])
            got.append(x["id"])
            if new:
                for w in sorted(self.waiters.pop(x["head"], ())):
                    self.ops["wake"] += 1
                    if w in self.pending:
                        self.pending[w].discard(x["head"])
                        if not self.pending[w]:
                            del self.pending[w]
                            stack.append(self.arts[w])
        for i in got:
            for old, new in self.retire_waits.pop(i, []):
                self.retire(self.arts[old], self.arts[new])

    def offer(self, a):
        self.arts[a["id"]] = a
        self.ops["offer"] += 1
        if not verified(a) or a["id"] in self.used:
            return
        self.st["pool"][str(a["id"])] = [a["head"], a["prem"]]
        self.ops["premise_check"] += len(a["prem"])
        reach = self.reach()
        miss = {p for p in a["prem"] if p not in reach}
        if not miss:
            self.admit(a); return
        self.pending[a["id"]] = miss
        for p in miss:
            self.waiters[p].add(a["id"])

    def retire(self, old, new):
        self.ops["retire_req"] += 1
        if not verified(old) or new is None:
            return
        self.arts[old["id"]] = old; self.arts[new["id"]] = new
        if old["id"] not in self.live or new["id"] not in self.live:
            wait = old["id"] if old["id"] not in self.live else new["id"]
            self.retire_waits[wait].append([old["id"], new["id"]]); return
        if new["head"] != old["head"]:
            return
        cone, stack, seen = {}, list(new["prem"]), set()
        while stack:
            h = stack.pop()
            if h in seen:
                continue
            seen.add(h)
            for i in self.provides[h]:
                if i != old["id"]:
                    self.ops["retire_check"] += 1
                    cone[i] = (self.arts[i]["head"], self.arts[i]["prem"])
                    stack.extend(self.arts[i]["prem"])
        after = closure(cone)
        if all(p in after for p in new["prem"]):
            self.st["log"].append(["retire", old["id"], new["id"]])
            self.live.discard(old["id"])
            self.provides[old["head"]].discard(old["id"])

    def dump(self):
        st = self.st
        st["arts"] = {str(k): v for k, v in self.arts.items()}
        st["live"] = sorted(self.live)
        st["pending"] = {str(k): sorted(v) for k, v in self.pending.items()}
        st["retire_waits"] = {str(k): v for k, v in self.retire_waits.items() if v}
        st["ops"] = dict(self.ops)
        st["reach"] = sorted(self.reach())
        return st

def spec(st, prev):
    arts = {int(k): v for k, v in st["arts"].items()}
    live = set(st["live"])
    rules = {i: (arts[i]["head"], arts[i]["prem"]) for i in live}
    reach = set(st["reach"])
    errs = []
    if closure(rules) != reach:
        errs.append("reach != closure of live rules")
    if closure({int(k): tuple(v) for k, v in st["pool"].items()}) != reach:
        errs.append("reach != closure of verified pool (unsaturated)")
    if not set(prev) <= reach:
        errs.append("reach shrank")
    return errs

st = load()
if args.summary:
    print(json.dumps({"batches": len(st["batches"]), "log": len(st["log"]), "live": len(st["live"]),
                      "reach": len(st["reach"]), "pending": len(st["pending"]), "ops": st["ops"],
                      "reach_sha256": hashlib.sha256("\n".join(st["reach"]).encode()).hexdigest(),
                      "live_ids_sha256": hashlib.sha256(",".join(map(str, st["live"])).encode()).hexdigest()},
                     sort_keys=True))
    sys.exit(0)

events = [json.loads(l) for l in open(args.events) if l.strip()]
order = []
for ev in events:
    if not order or order[-1] != ev["batch"]:
        order.append(ev["batch"])
targets = [args.batch] if args.batch else list(dict.fromkeys(order))
for b in targets:
    prev = list(st["reach"])
    eng = Engine(st)
    seen = set(st["seen"])
    applied = 0
    for ev in events:
        if ev["batch"] != b or key(ev) in seen:
            continue
        seen.add(key(ev)); applied += 1
        if ev["kind"] == "offer":
            eng.offer(ev["art"])
        else:
            eng.retire(ev["art"], ev.get("new"))
    st = eng.dump()
    st["seen"] = sorted(seen)
    errs = spec(st, prev)
    if errs:
        print(json.dumps({"batch": b, "refused": errs}))
        sys.exit(1)
    if applied:
        st["batches"].append(b)
    save(st)
    print(json.dumps({"batch": b, "applied": applied, "reach": len(st["reach"]),
                      "live": len(st["live"]), "pending": len(st["pending"])}, sort_keys=True))
