"""Gate for the monotone synthesis loop on real data.

Checks, each must hold for the result to count:
  spec      at every prefix of every order, incremental reach = reach of the log from
            scratch, = closure of the verified pool offered so far (saturated), and never
            shrinks; final reach identical across orders; retire cone check = full check.
  reference final reach (function capabilities) = an independent closure written here
            from the stream with the stated verifier (own grouping code, not the loop's).
  rerun     two runs of the same order print byte-identical JSON.
  controls  flipping one home's receipt removes exactly its capabilities; a non-covering
            retirement is refused; without grouping, mutual recursion stays blocked.
  mutants   each broken loop is caught by at least one order and check.
usage: gate.py stream.jsonl loop.py
"""
import json, subprocess, sys, tempfile, os
from collections import defaultdict

stream, loop = sys.argv[1], sys.argv[2]
ORDERS = ["history", "reverse", "shuffle:1", "shuffle:2", "shuffle:3"]
fails, out = [], []

def run(*a, dump=None):
    cmd = [sys.executable, "-I", loop, stream, *a]
    if dump:
        cmd += ["--dump-reach", dump]
    r = subprocess.run(cmd, capture_output=True, text=True)
    if r.returncode != 0:
        return None, r.stderr[-500:]
    return json.loads(r.stdout.strip().split("\n")[-1]), r.stdout

def check(name, ok, detail=""):
    out.append(f"{'PASS' if ok else 'FAIL'} {name}{(' ' + detail) if detail else ''}")
    if not ok:
        fails.append(name)

def spec_ok(d):
    return (d is not None and d["mismatch_log"] == 0 and d["unsaturated_prefixes"] == 0
            and d["monotone_breaks"] == 0 and not d["cone_vs_full_disagreements"]
            and d["pending_retire_at_end"] == 0)

# ---- independent reference: closure over verified artifacts, strongly connected groups
#      admitted together (Kosaraju, not the loop's Tarjan)
arts = [json.loads(l) for l in open(stream).read().split("\n")[1:] if l]
def ref_reach(verify):
    reach = set()
    for ver in ("0be14af", "f754884"):
        A = [a for a in arts if a["version"] == ver]
        g = {a["head"]: set(a["prem"]) for a in A}
        rg = defaultdict(set)
        for h, ps in g.items():
            for p in ps:
                rg[p].add(h)
        seen, order = set(), []
        for v in g:
            if v in seen:
                continue
            stack = [(v, iter(sorted(g[v])))]
            seen.add(v)
            while stack:
                x, it = stack[-1]
                nxt = next((w for w in it if w in g and w not in seen), None)
                if nxt is None:
                    order.append(x); stack.pop()
                else:
                    seen.add(nxt); stack.append((nxt, iter(sorted(g[nxt]))))
        comp, cid = {}, 0
        for v in reversed(order):
            if v in comp:
                continue
            st = [v]; comp[v] = cid
            while st:
                x = st.pop()
                for w in rg[x]:
                    if w in g and w not in comp:
                        comp[w] = cid; st.append(w)
            cid += 1
        members = defaultdict(list)
        for h in g:
            members[comp[h]].append(h)
        ok = {c: all(verify(a) for a in A if comp[a["head"]] == c) for c in members}
        # a group is admitted only if every member is verified (all share the home receipt)
        have, changed = set(), True
        while changed:
            changed = False
            for c, hs in members.items():
                if not ok[c] or all(h in have for h in hs):
                    continue
                ext = {p for h in hs for p in g[h] if comp.get(p) != c}
                if all(p in have or p in reach for p in ext):
                    have |= set(hs); changed = True
        reach |= have
    return reach

def verify_observed(a):
    return a["verdict"] == "PASSED" and a["observed"] in ("root", "reached")

# ---- spec, across orders
finals = {}
for o in ORDERS:
    with tempfile.NamedTemporaryFile("r", suffix=".txt", delete=False) as f:
        dump = f.name
    d, _ = run("--order", o, dump=dump)
    check(f"spec order={o}", spec_ok(d),
          "" if d is None else f"reach={d['reach']} live={d['live']} admitted={d['admitted']} retired={d['retired']} deferred={d['deferred_admissions']} inc={d['incremental_total']} cold_wl={d['cold_worklist_checks']} cold_naive={d['cold_naive_checks']}")
    finals[o] = (d or {}).get("reach_sha256")
    got = {h for h in open(dump).read().split("\n") if h and "<group" not in h}
    os.unlink(dump)
    if o == "history":
        ref = ref_reach(verify_observed)
        check("reference final reach = independent closure", got == ref, f"loop={len(got)} ref={len(ref)} diff={len(got ^ ref)}")
check("same final reach in every order", len(set(finals.values())) == 1, str(set(finals.values())))

# ---- rerun determinism
_, a1 = run("--order", "history", "--abstractions")
_, a2 = run("--order", "history", "--abstractions")
check("rerun byte-identical", a1 == a2)
ab = json.loads(a1.strip())["abstractions"]
check("abstractions leave reach unchanged", ab.get("reach_unchanged") is True,
      f"rules={ab.get('rules_added')} max_depth {ab.get('max_depth_before')}->{ab.get('max_depth_after')} sum_depth {ab.get('sum_depth_before')}->{ab.get('sum_depth_after')}")

# ---- controls
base, _ = run("--order", "history")
fl, _ = run("--order", "history", "--flip-home", "json")
json_heads = {a["head"] for a in arts if a["home"] == "json" and verify_observed(a)}
check("control flip json receipt: spec holds, json capabilities gone",
      spec_ok(fl) and fl["reach"] == base["reach"] - len(json_heads),
      f"reach {base['reach']} -> {fl['reach']} (json verified capabilities {len(json_heads)})")
fr, _ = run("--order", "history", "--fake-retire")
check("control non-covering retirement refused", spec_ok(fr) and fr["refusals"].get("not_covering") == 1,
      str(fr["refusals"]))
raw, _ = run("--order", "history", "--raw")
check("finding: without grouping, mutual recursion blocks admission",
      raw is not None and raw["pending_at_end"] > 0 and raw["mismatch_log"] == 0,
      f"pending={raw['pending_at_end']} admitted={raw['admitted']} vs grouped {base['admitted']}")
st, _ = run("--order", "history", "--strict")
check("strict verifier (direct battery application only): spec holds",
      st["mismatch_log"] == 0 and st["unsaturated_prefixes"] == 0 and st["monotone_breaks"] == 0 and not st["cone_vs_full_disagreements"],
      f"admitted={st['admitted']} live={st['live']} pending={st['pending_at_end']} pending_retire={st['pending_retire_at_end']}")

# ---- continuous ingest: one process per commit batch, state persisted, equals the one-shot run
ingest = os.path.join(os.path.dirname(os.path.abspath(loop)), "ingest.py")
with tempfile.TemporaryDirectory() as td:
    evp, stp = os.path.join(td, "events.jsonl"), os.path.join(td, "state.json")
    subprocess.run([sys.executable, "-I", loop, stream, "--emit-events", evp], capture_output=True, check=True)
    batches = list(dict.fromkeys(json.loads(l)["batch"] for l in open(evp) if l.strip()))
    ok_all = True
    for b in batches:
        r = subprocess.run([sys.executable, "-I", ingest, stp, evp, "--batch", b], capture_output=True, text=True)
        ok_all &= r.returncode == 0
    summ = json.loads(subprocess.run([sys.executable, "-I", ingest, stp, "--summary"], capture_output=True, text=True).stdout)
    check("ingest: one process per commit batch, spec holds after each", ok_all and summ["batches"] == len(batches),
          f"{len(batches)} batches, reach={summ['reach']} live={summ['live']} pending={summ['pending']}")
    check("ingest final state = one-shot run (reach and live ids)",
          summ["reach_sha256"] == base["reach_sha256"] and summ["live_ids_sha256"] == base["live_ids_sha256"])
    before = open(stp).read()
    subprocess.run([sys.executable, "-I", ingest, stp, evp, "--batch", batches[0]], capture_output=True)
    after = json.loads(open(stp).read()); b0 = json.loads(before)
    after.pop("batches"); b0.pop("batches")
    check("ingest: re-ingesting an applied batch changes nothing", after == b0)
    st = json.loads(before)
    victim = st["live"][0]
    st["live"] = st["live"][1:]
    st["seen"] = [k for k in st["seen"] if not k.startswith("offer:")]  # re-offer: forces a spec check
    json.dump(st, open(stp, "w"))
    r = subprocess.run([sys.executable, "-I", ingest, stp, evp, "--batch", batches[-1]], capture_output=True, text=True)
    check("control: a state that lost a live artifact is refused (reach would shrink)",
          r.returncode != 0 and "refused" in r.stdout, r.stdout.strip()[:120])

# ---- mutants: each must be caught somewhere
def caught(mutant, extra=()):
    for o in ORDERS:
        d, _ = run("--order", o, "--mutant", mutant, *extra)
        if d is None or not spec_ok(d):
            return o
        with tempfile.NamedTemporaryFile("r", suffix=".txt", delete=False) as f:
            dump = f.name
        run("--order", o, "--mutant", mutant, *extra, dump=dump)
        got = {h for h in open(dump).read().split("\n") if h and "<group" not in h}
        os.unlink(dump)
        if got != ref_reach(verify_observed):
            return o + " (reference)"
    return None

for m, extra in [("no-cover", ("--fake-retire",)), ("eager-retire", ()), ("no-premise-check", ()),
                 ("no-verifier", ()), ("no-retry", ())]:
    o = caught(m, extra)
    check(f"mutant {m} caught", o is not None, f"first caught at order {o}")

print("\n".join(out))
print("GATE", "FAIL " + ",".join(fails) if fails else "PASS", f"({len(out) - len(fails)}/{len(out)})")
sys.exit(1 if fails else 0)
