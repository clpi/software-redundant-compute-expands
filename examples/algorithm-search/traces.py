# Trace builders. Every trace is a list of canonical records
# (id, level, colors, premises, head) and is written with its sha256
# to the space log before any candidate runs on it.
#
# Dev traces (used to build and down-select):
#   estate   examples/worklist/EstateData.lean, 1,641 records
#   v2       examples/worklist/V2Data.lean, 3,630 records
# Held-out traces (declared before the down-select, built after it):
#   refs     reference graph of the 14 idol-lib v2 libraries at
#            master 578b8b3: one record per definition node, premises
#            = every candidate node of every reference it makes
#            (conjunctive), roots = definitions with no references.
#            New structure: it has reference cycles.
#   v2-rr    the v2 records, libraries interleaved round-robin
#            (a different real order of the same artifact).
# Decision data (families b-e):
#   dev      idol-eyes campaigns 1-4 raw.jsonl
#   held-out idol-eyes campaigns 5-6 raw.jsonl (new tasks, new driver)
import json, os, re, hashlib

HERE = os.path.dirname(os.path.abspath(__file__))
REC = re.compile(r"⟨(\d+), (\d+), \[([^\]]*)\], \[([^\]]*)\], (\d+)⟩")

def ints(s):
    return [int(x) for x in s.split(",") if x.strip()]

def lean_log(path):
    return [(int(a), int(b), ints(c), ints(d), int(e)) for a, b, c, d, e in REC.findall(open(path).read())]

def dev_closure():
    wl = os.path.join(HERE, "..", "worklist")
    return {"estate": lean_log(os.path.join(wl, "EstateData.lean")),
            "v2": lean_log(os.path.join(wl, "V2Data.lean"))}

def heldout_closure(idol_lib):
    libs = sorted(d for d in os.listdir(os.path.join(idol_lib, "graphs"))
                  if os.path.isfile(os.path.join(idol_lib, "graphs", d, "graph.json")))
    terms = {}
    def t(x):
        if x not in terms: terms[x] = len(terms)
        return terms[x]
    refs = []
    per_lib = []
    for lib in libs:
        g = json.load(open(os.path.join(idol_lib, "graphs", lib, "graph.json")))
        for n in g["nodes"]:
            if n["kind"] != "definition":
                continue
            ps = []
            for ref in n.get("references", []):
                ps += [t(c) for c in ref["candidates"]]
            refs.append((len(refs), 0, [2], ps, t(n["id"])))
        # v2 records of this library, as gen_v2.py encodes them
        terms2 = {}
        heads = {e["conclusion"] for e in g["edges"]}
        recs = []
        for n in g["nodes"]:
            if n["id"] not in heads:
                recs.append(([], n["id"]))
        for e in g["edges"]:
            recs.append((e["premises"], e["conclusion"]))
        per_lib.append(recs)
    # round-robin interleave of the per-library v2 record lists
    t2 = {}
    def u(x):
        if x not in t2: t2[x] = len(t2)
        return t2[x]
    rr, i = [], 0
    while any(per_lib):
        for recs in per_lib:
            if recs:
                ps, h = recs.pop(0)
                rr.append((len(rr), 0, [2], [u(p) for p in ps], u(h)))
    return {"refs": refs, "v2-rr": rr}

def digest(trace):
    return hashlib.sha256(json.dumps(trace).encode()).hexdigest()

# ---------------- decision data ----------------
DRIVERS_DISQUALIFIED = {"idol-map"}  # CLAIMS.md E3: replays recorded answers (REFUTED)

def campaign(path):
    rows = [json.loads(l) for l in open(path)]
    return rows

def options(rows):
    """One option per (task, driver) from cold runs: additive costs
    [cold_p50_us, cpu_p50_us, failures, warm_p50_us]. Disqualified
    drivers keep their records but carry color 'disqualified'."""
    import statistics
    cells = {}
    for r in rows:
        key = (r["task"], r["driver"])
        c = cells.setdefault(key, {"cold": [], "cpu": [], "fail": 0, "warm": []})
        if r["mode"] == "cold":
            c["cold"].append(r["wall_ms"]); c["cpu"].append(r.get("cpu_ms", 0.0))
            if not r.get("verified"):
                c["fail"] += 1
        elif r["mode"] == "warm":
            c["warm"].extend(r["task_ms"] if isinstance(r["task_ms"], list) else [r["task_ms"]])
    out = []
    for (task, drv), c in sorted(cells.items()):
        if not c["cold"] or not c["warm"]:
            continue
        vec = (round(statistics.median(c["cold"]) * 1000), round(statistics.median(c["cpu"]) * 1000),
               c["fail"], round(statistics.median(c["warm"]) * 1000))
        out.append({"task": task, "driver": drv, "cost": vec,
                    "disqualified": drv in DRIVERS_DISQUALIFIED})
    return out
