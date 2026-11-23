"""Continuous ingest: the monotone synthesis loop as a resumable process.

Each invocation loads the persisted state, applies one batch of new events (offers and
retirement requests, e.g. the receipts of one commit), checks the spec on the result, and
replaces the state file atomically while holding the same per-state writer lock. Nothing already admitted is revisited; a pending
candidate is retried exactly when its last missing premise lands, in this batch or a later
one. An exact event replay is a no-op. Reusing a key for different evidence is refused.

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
import argparse, fcntl, hashlib, json, os, sys, tempfile
from contextlib import contextmanager
from pathlib import Path
from collections import defaultdict

ap = argparse.ArgumentParser()
ap.add_argument("state")
ap.add_argument("events", nargs="?")
ap.add_argument("--batch", default="")
ap.add_argument("--summary", action="store_true")
args = ap.parse_args()
state_path = Path(args.state).resolve()

def key(ev):
    a = ev["art"]
    n = ev.get("new")
    return f'{ev["kind"]}:{a["id"]}:{n["id"] if n else "-"}'

def verified(a):
    return a["verdict"] == "PASSED" and a["observed"] in ("root", "reached")

def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)

def payload(ev):
    # Batch is scheduling metadata, not a second identity for the content.
    # Artifact bodies are checked against the immutable state table, not
    # duplicated in every event binding. Keep null-versus-absent distinctions.
    return canonical({k: (v["id"] if k in ("art", "new") and v is not None else v)
                      for k, v in ev.items() if k != "batch"})

def artifact_payload(a):
    return json.dumps({k: v for k, v in a.items() if k != "id"},
                      sort_keys=True, separators=(",", ":"), allow_nan=False)

def bind_ids(st, events):
    # Producer IDs name artifacts only in one incoming event file. Saved IDs
    # are append-only slots: historical log and pending references never move.
    incoming, indexed, used = {}, {}, set()
    for key, a in st["arts"].items():
        i = int(key)
        q = artifact_payload(a)
        if i != a["id"] or q in indexed:
            raise ValueError("ambiguous stored artifact identity")
        indexed[q] = i
        used.add(i)
    for ev in events:
        for a in (ev["art"], ev.get("new")):
            if a is None:
                continue
            i, q = a["id"], artifact_payload(a)
            if type(i) is not int or i < 0:
                raise ValueError("invalid producer artifact ID")
            if i in incoming and incoming[i] != q:
                raise ValueError("conflicting producer artifact ID: " + str(i))
            incoming[i] = q
    nxt = max(used | incoming.keys(), default=-1) + 1
    mapped = {}
    for i, q in sorted(incoming.items()):
        if q not in indexed:
            j = i
            if j in used:
                j = nxt
                nxt += 1
            indexed[q] = j
            used.add(j)
        mapped[i] = indexed[q]
    def remap(a):
        return dict(a, id=mapped[a["id"]]) if a is not None else None
    return [dict(ev, art=remap(ev["art"]),
                 **({"new": remap(ev["new"])} if "new" in ev else {}))
            for ev in events]

def fresh_state():
    return {"log": [], "arts": {}, "live": [], "pending": {}, "retire_waits": {},
            "pool": {}, "seen": {}, "batches": [], "ops": {}, "reach": []}

def load():
    if not state_path.exists():
        return fresh_state()
    with state_path.open() as f:
        st = json.load(f)
    if isinstance(st["seen"], list):
        if st["seen"] or st["log"] or st["batches"] or st["arts"]:
            raise ValueError("legacy state lacks event payloads; reconstruct to a new state")
        st["seen"] = {}
    if not isinstance(st["seen"], dict) or any(not isinstance(v, str) for v in st["seen"].values()):
        raise ValueError("invalid event binding store")
    return st

@contextmanager
def writer():
    # Never unlink the lock: a waiting process must share the same inode.
    with (state_path.parent / (state_path.name + ".lock")).open("a+b") as lock:
        fcntl.flock(lock.fileno(), fcntl.LOCK_EX)
        yield

def save(st):
    fd, tmp = tempfile.mkstemp(prefix=state_path.name + ".", suffix=".tmp",
                               dir=state_path.parent)
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(st, f, sort_keys=True, allow_nan=False)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, state_path)
        directory = os.open(state_path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if os.path.exists(tmp):
            os.unlink(tmp)

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

    def bind(self, a, replay):
        if a is None:
            return
        i = a["id"]
        if type(i) is not int or i < 0:
            raise ValueError("artifact identity must be a nonnegative integer")
        before = self.arts.get(i)
        if replay and before is None:
            raise ValueError(f"missing evidence for artifact {i} during replay")
        if before is not None and canonical(before) != canonical(a):
            raise ValueError(f"conflicting evidence for artifact {i}")
        self.arts[i] = a

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

if args.summary:
    # Rename exposes one complete prefix to readers; it is not a write.
    try:
        st = load()
    except ValueError as error:
        print(json.dumps({"refused": [str(error)]}), file=sys.stderr)
        sys.exit(1)
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
try:
    with writer():
        st = load()
        events = bind_ids(st, events)
        for b in targets:
            prev = list(st["reach"])
            eng = Engine(st)
            seen = st["seen"]
            applied = 0
            for ev in events:
                if ev["batch"] != b:
                    continue
                if ev["kind"] not in ("offer", "retire"):
                    raise ValueError("unknown event kind")
                k = key(ev)
                replay = k in seen
                eng.bind(ev["art"], replay)
                eng.bind(ev.get("new"), replay)
                body = payload(ev)
                if replay:
                    if seen[k] != body:
                        raise ValueError(f"conflicting replay for event {k}")
                    continue
                seen[k] = body
                applied += 1
                if ev["kind"] == "offer":
                    eng.offer(ev["art"])
                else:
                    eng.retire(ev["art"], ev.get("new"))
            st = eng.dump()
            errs = spec(st, prev)
            if errs:
                print(json.dumps({"batch": b, "refused": errs}))
                sys.exit(1)
            if applied:
                st["batches"].append(b)
                save(st)
            print(json.dumps({"batch": b, "applied": applied, "reach": len(st["reach"]),
                              "live": len(st["live"]), "pending": len(st["pending"])}, sort_keys=True))
except (ValueError, KeyError, TypeError, OSError) as error:
    print(json.dumps({"refused": [str(error)]}), file=sys.stderr)
    sys.exit(1)
