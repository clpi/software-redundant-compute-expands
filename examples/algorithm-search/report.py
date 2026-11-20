# Rebuild the report from the space log alone (the H3 rebuild test):
#   python3 report.py out/space.jsonl > REPORT.txt
# Checks the hash chain, counts candidates by how they were made, and
# prints every verdict with the measured values it rests on.
import collections, json, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from space import Space

S = Space(sys.argv[1])  # raises if the chain is broken
print("log records", len(S.recs), "chain head", S.prev)
cands = S.heads("candidate")
gen = collections.Counter()
for h in cands:
    rs = S.by_head(h)
    cs = set().union(*[set(r["colors"]) for r in rs])
    gen["product" if "generated:product" in cs else "parameter" if "generated:parameter" in cs else "seed"] += 1
measured = {r["head"][5:].split("|")[0] for r in S.with_color("measurement")}
print("candidate terms", len(cands), dict(gen), "measured", len(measured & set(cands)))
print("seeds that are also generated (one term, two derivations):",
      sorted(h for h in cands if len({c for r in S.by_head(h) for c in r["colors"]} & {"seed:reused", "generated:product"}) == 2))

M = collections.defaultdict(dict)
for r in S.with_color("measurement"):
    cand, inp, obj, ph = r["head"][5:].split("|")
    M[(cand, ph)][(inp, obj)] = r["receipt"]["value"]   # later attempts supersede

def summary(cand, ph):
    by = collections.defaultdict(list)
    for (inp, obj), v in M.get((cand, ph), {}).items():
        by[obj].append(v)
    out = []
    for obj, vs in sorted(by.items()):
        if all(isinstance(v, bool) for v in vs):
            out.append("%s %d/%d" % (obj, sum(vs), len(vs)))
        elif all(isinstance(v, (int, float)) for v in vs):
            out.append("%s sum %s [%s..%s] n=%d" % (obj, round(sum(vs), 3), round(min(vs), 3), round(max(vs), 3), len(vs)))
    return "; ".join(out)

for ph in ("dev", "heldout"):
    print("\n== verdicts, phase", ph)
    for r in S.with_color("verdict"):
        if not r["head"].endswith("|" + ph):
            continue
        cand = r["head"][len("verdict:"):-len(ph) - 1]
        v = [c for c in r["colors"] if c in ("survivor", "dominated", "incorrect")][0]
        doms = r["receipt"].get("dominated_by", [])
        print("%-10s %s%s" % (v, cand, ("  <- " + ", ".join(doms)) if doms else ""))
        print("           ", summary(cand, ph))

print("\n== controls (correctness on adversarial inputs)")
ctl = collections.defaultdict(lambda: [0, 0])
for (cand, ph), d in M.items():
    if ph != "control":
        continue
    for (inp, obj), v in d.items():
        if obj.startswith("correct"):
            ctl[cand][0] += v is True; ctl[cand][1] += 1
        if obj == "coverage":
            print("coverage", cand, inp, v)
for c, (a, b) in sorted(ctl.items()):
    print("correct %d/%d %s" % (a, b, c))

print("\n== validation")
for r in S.with_color("validation"):
    st = [c for c in r["colors"] if c != "validation"][0]
    print("%-26s %s" % (st, r["head"][len("validation:"):]))
