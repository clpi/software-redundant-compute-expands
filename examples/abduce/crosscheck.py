"""Reconcile the two abduction engines on main: this one (examples/abduce, Lean `Canon.Abduce`)
and #16's (examples/abduction, Lean `Canon.Abduction`). Same problems, both engines, both
checkers; the minimal explanation sets must be equal.

For every D0 instance (receipts/d0-planted.json) the log is rewritten as #16 input: each
record with premises is a rule, each abducible a hypothesis whose action is its own name, the
contradiction term is forbidden, the observations are the goals, every action costs 1. #16's
supports are computed by its abduction.py and accepted by its independent check_abduction.py;
this engine's explanations are its brute mirror of Lean `abduce` (all sizes, then the k = 3 cut
used by the ATMS). Reported: instances where the full sets agree, where the k <= 3 sets agree,
and #16 certificates its own checker accepts. Sensitivity control: the comparison is repeated
with one abducible that occurs in some explanation deleted from #16's input only; every such
mutant must disagree, or the agreement above would mean nothing.

Usage: crosscheck.py D0.json OUT.json
"""
import json, os, subprocess, sys, tempfile
from engine import brute

here = os.path.dirname(os.path.abspath(__file__))
pr16 = os.path.join(here, "..", "abduction")
d0, out = json.load(open(sys.argv[1])), sys.argv[2]
rows = []
for r in d0["rows"]:
    if "recs" not in r:
        continue
    names = r["names"]
    nm = lambda t: "bot" if t == 0 else names[t]
    records, i = [], 0
    for rec in r["recs"]:
        if rec["premises"]:
            records.append({"id": str(i), "kind": "rule", "head": nm(rec["head"]), "scope": "d0", "premises": [nm(p) for p in rec["premises"]]})
        else:
            records.append({"id": str(i), "kind": "fact", "head": nm(rec["head"]), "scope": "d0", "receipt": "d0"})
        i += 1
    for a in r["A"]:
        records.append({"id": str(i), "kind": "hypothesis", "head": names[a], "scope": "d0", "action": names[a]}); i += 1
    x = {"records": records, "query": {"scope": "d0", "goals": [names[o] for o in r["O"]], "forbidden": ["bot"],
                                       "dimensions": ["n"], "costs": {names[a]: [1] for a in r["A"]}}, "weights": [1]}
    def pr16_supports(x):
        with tempfile.TemporaryDirectory() as td:
            inp = os.path.join(td, "in.json")
            json.dump(x, open(inp, "w"))
            p = subprocess.run([sys.executable, os.path.join(pr16, "abduction.py"), inp], capture_output=True, text=True)
            return {frozenset(s["assumptions"]) for s in json.loads(p.stdout)["supports"]}
    with tempfile.TemporaryDirectory() as td:
        inp, cert = os.path.join(td, "in.json"), os.path.join(td, "cert.json")
        json.dump(x, open(inp, "w"))
        p = subprocess.run([sys.executable, os.path.join(pr16, "abduction.py"), inp], capture_output=True, text=True)
        if p.returncode != 0:
            rows.append({"seed": r["seed"], "error": p.stderr[-400:]}); continue
        open(cert, "w").write(p.stdout)
        c = subprocess.run([sys.executable, os.path.join(pr16, "check_abduction.py"), inp, cert], capture_output=True, text=True)
        theirs = {frozenset(s["assumptions"]) for s in json.loads(p.stdout)["supports"]}
    recs = [(tuple(rec["premises"]), rec["head"]) for rec in r["recs"]]
    from engine import Log
    lg = Log()
    for t in names[1:]:
        lg.atom(t)
    for rec in r["recs"]:
        lg.add([nm(q) if q else "⊥" for q in rec["premises"]], "⊥" if rec["head"] == 0 else names[rec["head"]])
    ours_all = {frozenset(names[a] for a in e) for e in brute(lg.recs, r["A"], r["O"], len(r["A"]))}
    ours_k3 = {e for e in ours_all if len(e) <= 3}
    used = sorted({a for e in ours_all for a in e})
    mutant = None
    if used:
        drop = used[r["seed"] % len(used)]
        xm = json.loads(json.dumps(x))
        xm["records"] = [q for q in xm["records"] if not (q["kind"] == "hypothesis" and q["action"] == drop)]
        xm["query"]["costs"].pop(drop)
        mutant = pr16_supports(xm) != ours_all
    rows.append({"seed": r["seed"], "ours": len(ours_all), "theirs": len(theirs), "agree_all": ours_all == theirs,
                 "agree_k3": ours_k3 == {e for e in theirs if len(e) <= 3}, "checker_accepts": c.returncode == 0, "mutant_disagrees": mutant,
                 "only_ours": sorted(map(sorted, ours_all - theirs))[:3], "only_theirs": sorted(map(sorted, theirs - ours_all))[:3]})
done = [r for r in rows if "error" not in r]
summary = {"instances": len(rows), "errors": len(rows) - len(done), "agree_all": sum(r["agree_all"] for r in done),
           "agree_k3": sum(r["agree_k3"] for r in done), "pr16_checker_accepts": sum(r["checker_accepts"] for r in done),
           "explanations_total": sum(r["ours"] for r in done),
           "mutants": sum(r["mutant_disagrees"] is not None for r in done), "mutants_detected": sum(bool(r["mutant_disagrees"]) for r in done)}
json.dump({"summary": summary, "rows": rows}, open(out, "w"), sort_keys=True, indent=0)
print(json.dumps(summary, sort_keys=True))
