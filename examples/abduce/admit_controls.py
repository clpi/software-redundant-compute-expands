"""Controls for admit.py: each tampering must be caught. Runs admit.py on copies of the real
receipts with one thing changed, and checks the outcome. Prints one line per control and exits 1
if any control is not caught.

Usage: admit_controls.py RECEIPTS_DIR CERTS_DIR GATES.jsonl RUNLOGS
"""
import json, os, shutil, subprocess, sys, tempfile

rec, certs, gates, runlogs = sys.argv[1:5]
here = os.path.dirname(os.path.abspath(__file__))


def admit(store, certs_dir, gates_path):
    p = subprocess.run([sys.executable, os.path.join(here, "admit.py"), store, rec, certs_dir, gates_path, runlogs], capture_output=True, text=True)
    try:
        return p.returncode, json.loads(p.stdout)
    except json.JSONDecodeError:
        return p.returncode, {"raw": p.stdout[-500:] + p.stderr[-500:]}


def copy_certs(w):
    d = os.path.join(w, "certs"); shutil.copytree(certs, d); return d


results, failed = [], 0


def check(name, ok, detail=""):
    global failed
    results.append((name, ok)); failed += 0 if ok else 1
    print(("caught " if ok else "MISSED ") + name + (f" :: {detail}" if detail else ""))


lines = [json.loads(l) for l in open(gates)]
with tempfile.TemporaryDirectory() as w:
    # baseline
    rc, base = admit(os.path.join(w, "s0.jsonl"), certs, gates)
    check("baseline admits and is append only and monotone", rc == 0 and base.get("monotone") and base.get("append_only"), f"admitted {len(base.get('admitted', []))}")
    admitted = set(base.get("admitted", []))

    # A1: a refuted trial relabeled VERIFIED (runs unchanged) must not be admitted
    t = [json.loads(json.dumps(g)) for g in lines]
    flipped = None
    for g in t:
        for rd in g["rounds"]:
            for x in rd.get("tested", []):
                for tr in x["trials"]:
                    if tr["verdict"] == "REFUTED" and flipped is None:
                        tr["verdict"] = "VERIFIED"; flipped = f"{g['gate']}:{x['cause']}"
    p1 = os.path.join(w, "g1.jsonl"); open(p1, "w").write("\n".join(json.dumps(g) for g in t) + "\n")
    rc, r = admit(os.path.join(w, "s1.jsonl"), certs, p1)
    check("A1 relabeled verdict", flipped and not any(flipped.split(":", 1)[1] in a and flipped.split(":", 1)[0] in a for a in r.get("admitted", [])), flipped or "no refuted trial")

    # A2: fabricated runs: a refuted trial's intervention symptoms emptied (logs unchanged)
    t = [json.loads(json.dumps(g)) for g in lines]
    fab = None
    for g in t:
        for rd in g["rounds"]:
            for x in rd.get("tested", []):
                for tr in x["trials"]:
                    if tr["verdict"] == "REFUTED" and fab is None:
                        for run in tr["intervention"]:
                            run["symptoms"] = [s for s in run["symptoms"] if s not in tr["target"]]
                        tr["verdict"] = "VERIFIED"; fab = f"{g['gate']}:{x['cause']}"
    p2 = os.path.join(w, "g2.jsonl"); open(p2, "w").write("\n".join(json.dumps(g) for g in t) + "\n")
    rc, r = admit(os.path.join(w, "s2.jsonl"), certs, p2)
    check("A2 fabricated run symptoms", fab and any(x.get("claim") == fab and "stored log" in str(x.get("reason")) for x in r.get("refused", [])), fab or "")

    # A3: a certificate output edited to hide sorryAx
    c3 = copy_certs(os.path.join(w, "c3"))
    name = next(json.loads(l)["name"] for l in open(os.path.join(c3, "certs.jsonl")) if not json.loads(l).get("expect_fail"))
    out = os.path.join(c3, name + ".out")
    open(out, "w").write(open(out).read().replace("[propext", "[propext, sorryAx"))
    rc, r = admit(os.path.join(w, "s3.jsonl"), c3, gates)
    check("A3 certificate output with sorryAx", f"minimal_explanation({name})" not in r.get("admitted", []), name)

    # A4: a claim naming a different hypothesis than its certificate
    c4 = copy_certs(os.path.join(w, "c4"))
    rows = [json.loads(l) for l in open(os.path.join(c4, "certs.jsonl"))]
    i = next(k for k, x in enumerate(rows) if not x.get("expect_fail") and len(x["hyp"]) >= 1)
    rows[i]["hyp"] = rows[i]["hyp"][:-1] if len(rows[i]["hyp"]) > 1 else rows[i]["hyp"] + rows[i]["hyp"]
    open(os.path.join(c4, "certs.jsonl"), "w").write("\n".join(json.dumps(x) for x in rows) + "\n")
    rc, r = admit(os.path.join(w, "s4.jsonl"), c4, gates)
    check("A4 claim with a different H", f"minimal_explanation({rows[i]['name']})" not in r.get("admitted", []), rows[i]["name"])

    # A5: a planted false hypothesis whose kernel refusal is replaced by a clean output
    c5 = copy_certs(os.path.join(w, "c5"))
    rows = [json.loads(l) for l in open(os.path.join(c5, "certs.jsonl"))]
    neg = next((x for x in rows if x.get("expect_fail")), None)
    if neg:
        open(os.path.join(c5, neg["name"] + ".out"), "w").write("'Canon.AbduceCert.minimal_explanation' depends on axioms: [propext]\n")
    rc, r = admit(os.path.join(w, "s5.jsonl"), c5, gates)
    check("A5 planted false hypothesis not refused by the kernel", neg is not None and rc == 1, neg["name"] if neg else "none")

    # A8: a delta-debugging run whose recorded failure is relabeled a pass: the narrowed set's
    # 1-minimality must no longer be admitted (its one-path removal is not shown to fail)
    t = [json.loads(json.dumps(g)) for g in lines]
    nm = None
    for g in t:
        for rd in g["rounds"]:
            m = (rd.get("narrowed") or {}).get("minimal")
            if m and nm is None:
                for x in rd["narrowed"]["tests"]:
                    if sorted(x["units"]) == sorted(m[1:]) or (len(m) == 1 and x["units"] == []):
                        x["rc"] = 0
                nm = f"minimal_prerequisite({g['gate']}, {', '.join(m)})"
    p8 = os.path.join(w, "g8.jsonl"); open(p8, "w").write("\n".join(json.dumps(g) for g in t) + "\n")
    rc, r = admit(os.path.join(w, "s8.jsonl"), certs, p8)
    check("A8 relabeled delta-debugging run", nm and nm in admitted and nm not in r.get("admitted", []), nm or "no narrowed set")

    # A9: a prerequisite step's log deleted from the run store: trials that cite it are refused
    t = [json.loads(json.dumps(g)) for g in lines]
    pre_h, who = None, None
    for g in t:
        for rd in g["rounds"]:
            for x in rd.get("tested", []):
                for tr in x["trials"]:
                    for run in tr["intervention"]:
                        if run.get("pre") and pre_h is None and tr["verdict"] in ("REPAIRED", "VERIFIED"):
                            pre_h, who = run["pre"][0]["log_sha256"], f"{g['gate']}:{x['cause']}"
    if pre_h:
        src = os.path.join(runlogs, pre_h + ".log"); keep = open(src).read(); os.remove(src)
        try:
            rc, r = admit(os.path.join(w, "s9.jsonl"), certs, gates)
        finally:
            open(src, "w").write(keep)
    check("A9 missing prerequisite-step log", pre_h and any(x.get("claim") == who and "stored log" in str(x.get("reason")) for x in r.get("refused", [])), who or "no prerequisite trial")

    # A10: the narrowed set's passing run swapped for a genuine failing log, rc left at 0
    # (the exit status is inside the hashed log, so the swap must be refused)
    t = [json.loads(json.dumps(g)) for g in lines]
    nm10 = None
    for g in t:
        for rd in g["rounds"]:
            nar = rd.get("narrowed") or {}
            m = nar.get("minimal")
            if m and nm10 is None:
                full = [x for x in nar["tests"] if sorted(x["units"]) == sorted(m) and x["rc"] == 0]
                bad = [x for x in nar["tests"] if x["rc"] != 0]
                if full and bad:
                    for x in full:
                        x["log_sha256"] = bad[0]["log_sha256"]
                    nm10 = f"minimal_prerequisite({g['gate']}, {', '.join(m)})"
    p10 = os.path.join(w, "g10.jsonl"); open(p10, "w").write("\n".join(json.dumps(g) for g in t) + "\n")
    rc, r = admit(os.path.join(w, "s10.jsonl"), certs, p10)
    check("A10 passing run swapped for a failing log", nm10 and nm10 in admitted and nm10 not in r.get("admitted", []), nm10 or "no narrowed set")

    # A11: an intervention run's exit status edited from failing to 0 (log unchanged)
    t = [json.loads(json.dumps(g)) for g in lines]
    who11 = None
    for g in t:
        for rd in g["rounds"]:
            for x in rd.get("tested", []):
                for tr in x["trials"]:
                    if tr["verdict"] == "REFUTED" and who11 is None and all(r_["rc"] != 0 for r_ in tr["intervention"]):
                        for r_ in tr["intervention"]:
                            r_["rc"] = 0; r_["symptoms"] = []
                        tr["verdict"] = "REPAIRED"; who11 = f"{g['gate']}:{x['cause']}"
    p11 = os.path.join(w, "g11.jsonl"); open(p11, "w").write("\n".join(json.dumps(g) for g in t) + "\n")
    rc, r = admit(os.path.join(w, "s11.jsonl"), certs, p11)
    check("A11 exit status edited to 0", who11 and any(x.get("claim") == who11 and "stored log" in str(x.get("reason")) for x in r.get("refused", [])), who11 or "no refuted trial")

    # A6: history rewrite of the store
    s6 = os.path.join(w, "s6.jsonl"); shutil.copy(os.path.join(w, "s0.jsonl"), s6)
    L = open(s6).read().splitlines()
    rr = json.loads(L[3]); b = json.loads(rr["body"]); b["head"] = b["head"] + "-edited"; rr["body"] = json.dumps(b, sort_keys=True)
    L[3] = json.dumps(rr, sort_keys=True); open(s6, "w").write("\n".join(L) + "\n")
    rc, r = admit(s6, certs, gates)
    check("A6 store history rewrite", rc != 0 and "chain broken" in r.get("raw", ""), r.get("raw", "")[-60:].strip())

    # A7: re-running admission on the admitted store appends nothing (idempotent, still append only)
    s7 = os.path.join(w, "s7.jsonl"); shutil.copy(os.path.join(w, "s0.jsonl"), s7)
    rc, r = admit(s7, certs, gates)
    check("A7 re-admission appends nothing", rc == 0 and r.get("store_after") == r.get("store_before"), f"{r.get('store_before')} -> {r.get('store_after')}")

print(f"admission controls: {sum(ok for _, ok in results)}/{len(results)} caught")
sys.exit(1 if failed else 0)
