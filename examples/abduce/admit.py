"""Admission: append only verified results to the abduction store, re-deciding every verdict
from its receipts. A second implementation, written apart from engine.py and gates.py: its own
closure, its own verdict rule, its own hash chain check. Nothing it is handed is trusted.

Store: STORE.jsonl, one record per line: {seq, prev, body, hash}, hash = sha256(prev + body).
Bodies:
  {"kind": "edge", "premises": [...], "head": "...", "colors": [...]}          domain records
  {"kind": "admit", "claim": "...", "premises": [...], "head": "...", "cites": {...}}

What is admitted:
  * D1 (formal): "H is a minimal explanation of O on log L@head" for each Lean certificate
    whose output shows exactly one axiom line within {propext, Classical.choice, Quot.sound}
    and no error, whose file names the same H, O and records as the domain result, and whose
    claim this module's own closure confirms (explains, consistent, erase-one minimal).
  * D2 (empirical): "cause C produced symptom s of gate G" when, recomputed from the run
    records (never from the verdict field), s is in every control run, in no intervention run,
    and in every placebo run. "Repaired" additionally needs exit 0 in every intervention run.
    Placeholder interventions (an empty file) are admitted only as "fail point" claims.
Refused: everything else, including every planted false cause.

Checks on every call: the old store is a hash-valid prefix of the new one (append only), and
the closure of the old edges is contained in the closure of the new edges (monotone).

Usage: admit.py STORE.jsonl RECEIPTS_DIR CERTS_DIR GATES.jsonl > admit.json   (exit 1 on any failure)
"""
import hashlib, json, os, re, sys

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def H(s):
    return hashlib.sha256(s.encode()).hexdigest()


def load(store):
    recs = []
    if os.path.exists(store):
        for line in open(store):
            recs.append(json.loads(line))
    prev = "0" * 64
    for i, r in enumerate(recs):
        if r["seq"] != i or r["prev"] != prev or r["hash"] != H(prev + r["body"]):
            raise SystemExit(f"store chain broken at {i}")
        prev = r["hash"]
    return recs


def close(edges, roots=()):
    S, changed = set(roots), True
    while changed:
        changed = False
        for p, h in edges:
            if h not in S and all(x in S for x in p):
                S.add(h); changed = True
    return S


def edges_of(recs):
    out = []
    for r in recs:
        b = json.loads(r["body"])
        out.append((tuple(b["premises"]), b["head"]))
    return out


def fisher_greater(a, n1, b, n2):
    """One-sided Fisher exact p (written here again, not imported: the verdict rule is re-derived)."""
    from math import comb
    k = a + b
    return sum(comb(n1, i) * comb(n2, k - i) for i in range(a, min(n1, k) + 1) if 0 <= k - i <= n2) / comb(n1 + n2, k)


def main():
    store, rec_dir, cert_dir, gates_path = sys.argv[1:5]
    runlogs = sys.argv[5] if len(sys.argv) > 5 else None
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from gates import symptoms as extract  # the one shared piece: the symptom extractor (a stated premise)

    def run_ok(r):
        """The run's log exists, hashes to its recorded hash, and yields the recorded symptoms."""
        if not runlogs:
            return False
        p = os.path.join(runlogs, r["log_sha256"] + ".log")
        if not os.path.exists(p):
            return False
        txt = open(p).read()
        return H(txt) == r["log_sha256"] and extract(txt, r["rc"], {}) == r["symptoms"] and all(log_ok(q["log_sha256"]) for q in r.get("pre", []))

    def log_ok(h):
        p = os.path.join(runlogs, h + ".log") if runlogs else ""
        return bool(runlogs) and os.path.exists(p) and H(open(p).read()) == h
    old = load(store)
    old_bodies = {r["body"] for r in old}
    new_bodies, report = [], {"admitted": [], "refused": []}

    def append(body):
        s = json.dumps(body, sort_keys=True)
        if s not in old_bodies and s not in new_bodies:
            new_bodies.append(s)

    # ---- domain records (the D1 logs, colored by mode); identical edges keep one record per color set
    logs = {}
    for mode in ("strict", "raw"):
        d = json.load(open(os.path.join(rec_dir, f"d1-{mode}.json")))
        logs[f"d1-{mode}.json"] = d
        for r in d["recs"]:
            append({"kind": "edge", "premises": [d["names"][x] for x in r["premises"]], "head": d["names"][r["head"]], "colors": [f"d1:{mode}"]})

    # ---- D1: Lean certificates
    for line in open(os.path.join(cert_dir, "certs.jsonl")):
        c = json.loads(line)
        why = []
        lean = os.path.join(cert_dir, c["name"] + ".lean"); out = os.path.join(cert_dir, c["name"] + ".out")
        if c.get("expect_fail"):
            # a planted false hypothesis: it must have been refused by the kernel
            txt = open(out).read() if os.path.exists(out) else ""
            if "error" in txt and "decide" in txt:
                report["refused"].append({"claim": c["name"], "reason": "planted false: kernel refused (as required)"})
            else:
                why.append("planted false hypothesis was NOT refused by the kernel")
                report["refused"].append({"claim": c["name"], "reason": why})
            continue
        if not (os.path.exists(lean) and os.path.exists(out)):
            report["refused"].append({"claim": c["name"], "reason": "missing certificate files"}); continue
        if hashlib.sha256(open(lean, "rb").read()).hexdigest() != c["file_sha256"]:
            why.append("certificate file hash differs")
        txt = open(out).read()
        ax = [l for l in txt.splitlines() if "depends on axioms" in l or "does not depend on any axioms" in l]
        used = set()
        for l in ax:
            m = re.search(r"\[([^\]]*)\]", l)
            if m:
                used |= {a.strip() for a in m.group(1).split(",") if a.strip()}
        if "error" in txt or len(ax) != 1 or not used <= ALLOWED:
            why.append(f"lean output not clean: axioms {sorted(used)}")
        src = os.path.join(rec_dir, c["domain"]) if c["domain"] in logs else os.path.join(cert_dir, c["domain"])
        d = logs.get(c["domain"]) or json.load(open(src))
        ids = {n: i for i, n in enumerate(d["names"])}
        Hs = sorted(ids[x] for x in c["hyp"]); Os = [ids[x] for x in c["obs"]]
        body = open(lean).read()
        if f"def H : List Nat := [{', '.join(map(str, Hs))}]" not in body:
            why.append("certificate names a different H")
        if f"fun _ => true, 0, [{', '.join(map(str, Hs))}], [{', '.join(map(str, Os))}]⟩" not in body:
            why.append("certificate names a different O")
        recs_txt = ",\n".join(f"  ⟨{r['id']}, 0, [], [{', '.join(map(str, r['premises']))}], {r['head']}⟩" for r in d["recs"])
        if "def L : List Rec := [\n" + recs_txt + "\n]" not in body:
            why.append("certificate log differs from the domain log")
        E = [(tuple(r["premises"]), r["head"]) for r in d["recs"]]
        S = close(E, Hs)
        if not (all(o in S for o in Os) and 0 not in S):
            why.append("own closure: not an explanation")
        for x in Hs:
            Sx = close(E, [y for y in Hs if y != x])
            if all(o in Sx for o in Os):
                why.append("own closure: not minimal")
        claim = f"minimal_explanation({c['name']})"
        if why:
            report["refused"].append({"claim": claim, "reason": why}); continue
        log_head = d.get("log_head", "")
        append({"kind": "admit", "claim": claim, "premises": [f"lean:{c['file_sha256']}"], "head": claim,
                "cites": {"certificate_sha256": c["file_sha256"], "lean_output_sha256": hashlib.sha256(open(out, "rb").read()).hexdigest(),
                          "domain": c["domain"], "log_head": log_head, "H": c["hyp"], "O": c["obs"]}})
        append({"kind": "edge", "premises": [], "head": f"lean:{c['file_sha256']}", "colors": ["receipt:lean"]})
        report["admitted"].append(claim)

    # ---- D2: experiments, verdicts recomputed from run records
    for line in open(gates_path):
        g = json.loads(line)
        for rd in g["rounds"]:
            ctrl = rd.get("control", [])
            art = [{"cause": rd["artifact"]["cause"], "trials": rd["artifact"]["trials"]}] if rd.get("artifact") else []
            for t in rd.get("tested", []) + art:
                for tr in t["trials"]:
                    target = tr["target"]
                    ctrl = rd.get("control", []) + tr.get("control_extra", [])
                    allruns = ctrl + tr["intervention"] + tr["placebo"]
                    if not all(run_ok(r) for r in allruns):
                        report["refused"].append({"claim": f"{g['gate']}:{t['cause']}", "reason": "a run record does not match its stored log"}); continue
                    hit = lambda r: all(s in r["symptoms"] for s in target)
                    pc = all(map(hit, ctrl)) and len(ctrl) >= 2
                    gone = all(not any(s in r["symptoms"] for s in target) for r in tr["intervention"]) and len(tr["intervention"]) >= 2
                    pp = all(map(hit, tr["placebo"])) and len(tr["placebo"]) >= 2
                    if not pc and any(map(hit, ctrl)) and gone:  # flaky gate: the statistical rule
                        c, q, ni = sum(map(hit, ctrl)), sum(map(hit, tr["placebo"])), len(tr["intervention"])
                        pc = fisher_greater(c, len(ctrl), 0, ni) < 0.05
                        pp = fisher_greater(q, len(tr["placebo"]), 0, ni) < 0.05
                    acquired = tr["why"].startswith("run the hidden step")
                    placeholder = tr["why"].startswith("empty placeholder")
                    repaired = gone and all(r["rc"] == 0 for r in tr["intervention"])
                    claimed = tr["verdict"]
                    if acquired:
                        report["refused"].append({"claim": f"{g['gate']}:{t['cause']}", "reason": "observation acquisition, not a causal claim"}); continue
                    if not (pc and gone and pp):
                        r_ = {"claim": f"{g['gate']}:{t['cause']}", "reason": "recomputed: not verified", "claimed_verdict": claimed}
                        if claimed in ("VERIFIED", "REPAIRED"):
                            r_["reason"] = "recomputed verdict disagrees with the recorded one"
                        report["refused"].append(r_); continue
                    kind = "fail_point" if placeholder else ("repaired" if repaired else "cause")
                    claim = f"{kind}({g['gate']}, {t['cause']} -> {', '.join(target)})"
                    runs = [r["log_sha256"] for r in allruns]
                    for h in runs:
                        append({"kind": "edge", "premises": [], "head": f"run:{h}", "colors": ["receipt:run"]})
                    append({"kind": "admit", "claim": claim, "premises": [f"run:{h}" for h in runs], "head": claim,
                            "cites": {"gate": g["gate"], "round": rd["round"], "intervention": tr["why"], "target": target}})
                    report["admitted"].append(claim)
            # 1-minimality of a narrowed artifact set, recomputed from the delta-debugging runs:
            # the set alone repairs, and removing any one of its paths does not
            nar = rd.get("narrowed") or {}
            m = nar.get("minimal")
            if m:
                tests = nar["tests"]
                key = lambda us: tuple(sorted(us))
                ok_full = [x for x in tests if key(x["units"]) == key(m) and x["rc"] == 0 and log_ok(x["log_sha256"])]
                drops = {u: [x for x in tests if key(x["units"]) == key([v for v in m if v != u])] for u in m}
                ok_drop = all(xs and all(x["rc"] != 0 and log_ok(x["log_sha256"]) for x in xs) for xs in drops.values())
                claim = f"minimal_prerequisite({g['gate']}, {', '.join(m)})"
                if ok_full and ok_drop:
                    hs = [ok_full[0]["log_sha256"]] + [xs[0]["log_sha256"] for xs in drops.values()]
                    for h in hs:
                        append({"kind": "edge", "premises": [], "head": f"run:{h}", "colors": ["receipt:run"]})
                    append({"kind": "admit", "claim": claim, "premises": [f"run:{h}" for h in hs], "head": claim,
                            "cites": {"gate": g["gate"], "round": rd["round"], "units": m}})
                    report["admitted"].append(claim)
                else:
                    report["refused"].append({"claim": claim, "reason": "recomputed: set does not repair alone, or some one-path removal was not shown to fail"})

    # ---- append only and monotone
    recs = list(old)
    prev = recs[-1]["hash"] if recs else "0" * 64
    for b in new_bodies:
        h = H(prev + b)
        recs.append({"seq": len(recs), "prev": prev, "body": b, "hash": h})
        prev = h
    before, after = close(edges_of(old)), close(edges_of(recs))
    report["monotone"] = before <= after
    report["append_only"] = [r["hash"] for r in recs[:len(old)]] == [r["hash"] for r in old]
    report["store_before"], report["store_after"] = len(old), len(recs)
    report["head"] = prev
    if not (report["monotone"] and report["append_only"]):
        print(json.dumps(report, indent=1)); raise SystemExit(1)
    with open(store, "w") as f:
        for r in recs:
            f.write(json.dumps(r, sort_keys=True) + "\n")
    bad = [r for r in report["refused"] if isinstance(r["reason"], list) and any("NOT refused" in x for x in r["reason"])]
    print(json.dumps(report, indent=1, sort_keys=True))
    raise SystemExit(1 if bad else 0)


if __name__ == "__main__":
    main()
