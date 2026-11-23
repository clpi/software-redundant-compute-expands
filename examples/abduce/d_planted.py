"""Domain D0: planted causes on random logs.

Each instance: a random record log over n terms, abducibles A, a planted true cause H* (1 to 3
abducibles). Observations are terms H* derives that nothing derives without assumptions;
negative observations are terms H* does not derive, entered as `term -> bot`. Three planted
false hypotheses per instance: a same-size set that does not explain, H* plus an abducible that
derives a negatively observed term (inconsistent), and H* plus an abducible that changes nothing
(not minimal).

Measured per instance, with the log appended one record at a time:
  * incremental ATMS explanations == brute-force mirror of Lean `abduce`, after EVERY append;
  * work: ATMS unions+visits accumulated vs rebuilding the ATMS from scratch after every append;
  * recovery: the planted cause's minimal core is among the minimal explanations; it is the
    unique cheapest; rank of the core among the explanations by (cost, size);
  * rejection: each planted false hypothesis fails `minimal` (the Lean `minimalB` mirror).

Usage: d_planted.py N OUT.json
"""
import json, random, sys
from engine import Log, ATMS, brute, closure, minimal

N, out = int(sys.argv[1]), sys.argv[2]
rows = []
for seed in range(N):
    R = random.Random(seed)
    n = R.randint(14, 40)
    lg = Log()
    terms = [lg.atom(f"t{i}") for i in range(n)]
    A = R.sample(terms, R.randint(5, 10))
    inner = [t for t in terms if t not in A]
    recs = []
    for _ in range(R.randint(n, 2 * n)):
        ps = R.sample(terms, R.randint(1, 3))
        h = R.choice(inner)
        recs.append((ps, h))
    for ps, h in recs:
        lg.add([lg.names[p] for p in ps], lg.names[h])
    Hs = R.sample(A, R.randint(1, 3))
    S_true = closure(lg.recs, Hs)
    S_none = closure(lg.recs, [])
    pos = [t for t in inner if t in S_true and t not in S_none]
    if not pos:
        rows.append({"seed": seed, "skipped": "planted cause derives nothing observable"}); continue
    nobs = R.randint(1, min(4, len(pos)))
    O = R.sample(pos, nobs)
    negs = [t for t in inner if t not in S_true]
    neg = R.sample(negs, min(len(negs), R.randint(0, 3)))
    for t in neg:
        lg.add([lg.names[t]], "⊥")
    k = 3
    # incremental vs scratch, checked after every append
    at = ATMS(A, k)
    scratch_ops, agree, prefixes = 0, True, 0
    for i, r in enumerate(lg.recs):
        at.add(r)
        prefixes += 1
        sc = ATMS(A, k)
        for r2 in lg.recs[:i + 1]:
            sc.add(r2)
        scratch_ops += sc.ops["union"] + sc.ops["visit"]
        inc = set(at.explanations(O))
        if inc != set(sc.explanations(O)) or inc != brute(lg.recs[:i + 1], A, O, k):
            agree = False
    ex = set(at.explanations(O))
    # minimal core of the planted cause
    core = list(Hs)
    for x in list(core):
        t = [y for y in core if y != x]
        S = closure(lg.recs, t)
        if 0 not in S and all(o in S for o in O):
            core = t
    core = frozenset(core)
    ranked = sorted(ex, key=lambda e: (len(e), sorted(e)))
    cheapest = [e for e in ranked if len(e) == len(ranked[0])] if ranked else []
    # planted false hypotheses
    others = [a for a in A if a not in Hs]
    false = []
    for _ in range(20):
        F = R.sample(A, len(Hs))
        S = closure(lg.recs, F)
        if not all(o in S for o in O):
            false.append(("does-not-explain", F)); break
    bad = [a for a in others if any(t in closure(lg.recs, Hs + [a]) for t in neg)]
    if bad:
        false.append(("inconsistent", Hs + [bad[0]]))
    idle = [a for a in others if a not in bad]
    if idle:
        false.append(("not-minimal", list(core) + [idle[0]]))
    rejected = {kind: not minimal(lg.recs, A, O, F) for kind, F in false}
    rows.append({
        "seed": seed, "terms": n, "records": len(lg.recs), "abducibles": len(A), "planted": sorted(lg.names[x] for x in Hs),
        "core": sorted(lg.names[x] for x in core), "observations": len(O), "negatives": len(neg),
        "explanations": len(ex), "agree_every_prefix": agree, "prefixes": prefixes,
        "core_recovered": core in ex, "core_unique_cheapest": cheapest == [core], "core_rank": ranked.index(core) + 1 if core in ex else None,
        "incremental_ops": at.ops["union"] + at.ops["visit"], "scratch_ops": scratch_ops,
        "false": [{"kind": kind, "hyp": sorted(lg.names[x] for x in F), "rejected": rejected[kind]} for kind, F in false],
        "names": lg.names, "recs": lg.recs, "A": A, "O": O, "core_ids": sorted(core),
    })

done = [r for r in rows if "skipped" not in r]
summary = {
    "instances": N, "used": len(done), "skipped": N - len(done),
    "agree_every_prefix": sum(r["agree_every_prefix"] for r in done), "prefixes_checked": sum(r["prefixes"] for r in done),
    "core_recovered": sum(r["core_recovered"] for r in done),
    "core_unique_cheapest": sum(r["core_unique_cheapest"] for r in done),
    "core_rank_hist": {str(k_): sum(1 for r in done if r["core_rank"] == k_) for k_ in sorted({r["core_rank"] for r in done}, key=lambda x: (x is None, x))},
    "false_total": sum(len(r["false"]) for r in done),
    "false_rejected": sum(f["rejected"] for r in done for f in r["false"]),
    "false_by_kind": {kind: [sum(1 for r in done for f in r["false"] if f["kind"] == kind and f["rejected"]),
                             sum(1 for r in done for f in r["false"] if f["kind"] == kind)] for kind in ("does-not-explain", "inconsistent", "not-minimal")},
    "unique_by_observations": {str(m): [sum(1 for r in done if r["observations"] == m and r["core_unique_cheapest"]), sum(1 for r in done if r["observations"] == m)] for m in range(1, 5)},
    "incremental_ops": sum(r["incremental_ops"] for r in done), "scratch_ops": sum(r["scratch_ops"] for r in done),
}
json.dump({"summary": summary, "rows": rows}, open(out, "w"), sort_keys=True)
print(json.dumps(summary, sort_keys=True))
