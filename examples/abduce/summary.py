"""Headline numbers from the receipts (every number in README.md and the ledger comes from here)."""
import json, os, sys

R = sys.argv[1]
d0 = json.load(open(os.path.join(R, "d0-planted.json")))["summary"]
s = json.load(open(os.path.join(R, "d1-strict.json")))
w = json.load(open(os.path.join(R, "d1-raw.json")))
certs = [json.loads(l) for l in open(os.path.join(R, "certs", "certs.jsonl"))]
gates = [json.loads(l) for l in open(os.path.join(R, "gates.jsonl"))]
adm = json.load(open(os.path.join(R, "admit.json")))


def trials(g):
    return [(rd["round"], x["cause"], t["verdict"], t["why"]) for rd in g["rounds"] for x in rd.get("tested", []) for t in x["trials"]]


real = [g for g in gates if not g["gate"].startswith("planted/")]
planted = [g for g in gates if g["gate"].startswith("planted/")]
spec = {g["name"]: g for g in json.load(open(os.environ.get("GATES_SPEC", os.path.join(os.path.dirname(os.path.abspath(__file__)), "gates-public.json"))))}
out = {
    "d0_planted": d0,
    "d1_strict": {"pending_all": s["pending_all"], "pending_live": s["pending_live"], "components": s["components"],
                  "no_explanation_at_k3": len(s["obs_without_explanation_at_k"]), "plan_final": s["plan"][-1] if s["plan"] else None,
                  "plan_first": s["plan"][0] if s["plan"] else None, "front_size": len(s["front"])},
    "d1_raw": {"pending": w["pending_all"], "explanation": w["front"][0]["hyp"], "covers": w["front"][0]["cover"], "kind": w["front"][0]["kind"]},
    "certificates": {"certified": sum(c["ok"] for c in certs if not c.get("expect_fail")), "of": sum(1 for c in certs if not c.get("expect_fail")),
                     "false_refused": sum(c["ok"] for c in certs if c.get("expect_fail")), "false_of": sum(1 for c in certs if c.get("expect_fail")),
                     "seconds_total": round(sum(c.get("seconds") or 0 for c in certs), 1)},
    "gates_real": {g["gate"]: {"status": g["status"], "trials": trials(g)} for g in real},
    "gates_planted": {g["gate"]: {"status": g["status"], "planted": spec.get(g["gate"], {}).get("planted"),
                                  "first_verified": next((c for (_, c, v, why) in trials(g) if v in ("REPAIRED", "VERIFIED") and not why.startswith("empty")), None),
                                  "trials": trials(g)} for g in planted},
    "planted_false_refuted": sum(1 for g in gates for (_, c, v, _w) in trials(g) if c in {f["name"] for f in spec.get(g["gate"], {}).get("false", [])} and v == "REFUTED"),
    "planted_false_tested": sum(1 for g in gates for (_, c, v, _w) in trials(g) if c in {f["name"] for f in spec.get(g["gate"], {}).get("false", [])}),
    "admission": {"admitted": len(adm["admitted"]), "refused": len(adm["refused"]), "store_records": adm["store_after"], "head": adm["head"],
                  "monotone": adm["monotone"], "append_only": adm["append_only"]},
}
json.dump(out, open(os.path.join(R, "SUMMARY.json"), "w"), indent=1, sort_keys=True)
print(json.dumps(out, indent=1, sort_keys=True))
