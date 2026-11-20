# Same-contract algorithm search over one append-only hypergraph.
#   python3 run_search.py dev OUT_DIR          build the space, measure on dev, down-select
#   python3 run_search.py heldout OUT_DIR IDOL_LIB
#                                              re-validate survivors (held-out + controls)
# Everything (components, generated candidates, traces, objectives,
# measurements, verdicts) is a record of OUT_DIR/space.jsonl. The
# report is printed from that log alone (report.py).
import gc, itertools, json, os, statistics, sys, time, tracemalloc, random
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import closure, decide, traces
from space import Space, sha

EYES = os.environ.get("EYES_DIR", "/mnt/project-files/idol-eyes")
REPEATS = int(os.environ.get("REPEATS", "5"))

def timed(fn, repeats=REPEATS):
    ws = []
    for _ in range(repeats):
        gc.collect()
        t = time.perf_counter(); out = fn(); ws.append((time.perf_counter() - t) * 1000)
    q = statistics.quantiles(ws, n=4) if len(ws) > 1 else [ws[0]] * 3
    return out, {"median": statistics.median(ws), "p25": q[0], "p75": q[2], "runs": ws}

def peak(fn):
    gc.collect(); tracemalloc.start()
    fn()
    _, p = tracemalloc.get_traced_memory(); tracemalloc.stop()
    return round(p / 1024, 1)

# ------------------------------------------------------------------
# Components, constraints, generation
# ------------------------------------------------------------------
PRIOR = {
 "comp:a/trigger=counter": "Dowling & Gallier 1984 (linear-time Horn satisfiability); semi-naive Datalog core. Proof: proof/Worklist.lean (c49c546)",
 "comp:a/trigger=watch": "watched literals, Moskewicz et al. 2001 (Chaff), adapted to Horn rules here",
 "comp:a/trigger=delta": "semi-naive evaluation, Bancilhon 1986",
 "comp:a/trigger=rounds": "naive fixpoint iteration (Kleene)",
 "comp:a/trigger=scratch": "naive recomputation from empty",
 "comp:b/front=sortfilter": "maxima of a point set, Kung, Luccio & Preparata 1975 (sort then filter)",
 "comp:b/front=archive": "online Pareto archive (standard in multi-objective search)",
 "comp:b/joint=fold": "multi-objective dynamic programming, Hansen 1980 (bicriterion paths); srce PR 3 / idol-eyes plan.id",
 "comp:b/select=ch": "weighted Chebyshev reaches every Pareto point, Bowman 1976; Steuer & Choo 1983",
 "comp:b/select=ach": "augmented Chebyshev excludes weakly dominated picks, Steuer & Choo 1983",
 "comp:b/select=ws": "weighted sum reaches supported points only, Das & Dennis 1997",
 "comp:b/select=eps": "epsilon-constraint, Haimes, Lasdon & Wismer 1971",
 "comp:b/select=lex": "lexicographic optimization",
 "comp:c/stop=bound": "branch-and-bound pruning bound applied as a stop test",
 "comp:c/stop=bestfirst": "k-best enumeration, Lawler 1972",
 "comp:a/reference": "superior-function shortest paths, Knuth 1977",
}

def components(S):
    axes = {
        "a": {"trigger": ["scratch", "rounds", "delta", "counter", "watch"], "dedup": ["on", "off"], "check": ["short", "full"]},
        "b1": {"front": ["pairwise", "sortfilter", "archive"]},
        "b2": {"joint": ["brute", "fold"], "prune": ["on", "off"]},
        "b3": {"select": ["ws", "ch", "ach", "eps", "lex"], "scope": ["direct", "frontfirst"]},
        "c": {"stop": ["threshold", "exhaustive", "bound", "bestfirst"]},
        "d": {"rescoring": ["archive", "cold-sortfilter", "cold-pairwise"]},
        "f": {"resolver": ["name", "visible", "nearest", "enclosing"]},
    }
    for fam, ax in axes.items():
        for a, vals in ax.items():
            for v in vals:
                h = "comp:%s/%s=%s" % (fam, a, v)
                S.append(h, [], ["component", "family:" + fam], {"prior_work": PRIOR.get(h, "")})
    # structural constraints, as records: a component that does not
    # apply under another is dropped from the canonical key
    rules = [("comp:a/check=*", "comp:a/trigger=counter", "not applicable: counters never re-test readiness"),
             ("comp:a/check=*", "comp:a/trigger=watch", "not applicable: the watch scan has no readiness test"),
             ("comp:b2/prune=*", "", "applies to both joint modes"),]
    for drop, under, why in rules:
        S.append("rule:drop %s under %s" % (drop, under or "-"), [], ["constraint"], {"why": why})
    return axes

def generate(S, axes):
    """Product of each family's axes, canonicalized by the constraint
    records; colliding keys become a second derivation of one term."""
    made = {}
    for fam, ax in axes.items():
        names = list(ax)
        for combo in itertools.product(*[ax[n] for n in names]):
            c = dict(zip(names, combo))
            if fam == "a" and c["trigger"] in ("counter", "watch"):
                c["check"] = "-"
            key = "cand:%s/" % fam + ",".join("%s=%s" % (n, c[n]) for n in names)
            prem = ["comp:%s/%s=%s" % (fam, n, combo[i]) for i, n in enumerate(names)]
            colors = ["candidate", "family:" + fam, "generated:product"]
            if key in made:
                colors.append("collapsed")
            S.append(key, prem, colors, {"components": c})
            made[key] = c
    seeds = {"cand:a/trigger=counter,dedup=on,check=-": "proved in proof/Worklist.lean (c49c546)",
             "cand:b3/select=ch,scope=frontfirst": "idol-eyes PR 19 frontier-first act",
             "cand:b2/joint=fold,prune=on": "srce PR 3 / idol-eyes plan.id factored joint plans",
             "cand:c/stop=exhaustive": "idol-eyes PR 19 certified stop (every alternative seen)",
             "cand:c/stop=threshold": "idol-eyes eyes.id acceptance stop"}
    for k, why in seeds.items():
        S.append(k, [], ["candidate", "seed:reused", "family:" + k.split(":")[1].split("/")[0]], {"source": why})
    return made

def external(S):
    """Chris's software-is-reversible results (10:00Z): recorded as
    claims, not measured here (the bundle did not reach this project)."""
    claims = [
        ("ext:reversible/compose-first-residual", "exact whole-trace residual 5 bits vs 10 with per-step worst case, one finite trace family; decoder not counted"),
        ("ext:reversible/exact-front-24576", "exact Pareto front over 24,576 designs, 6 synthetic families; separate optimizer matched; 480 frontier steps reversed"),
        ("ext:reversible/incremental-optimizer", "matched cold recomputation at 72 append prefixes with 1,760 vs 3,488 search extensions (operation counts)"),
        ("ext:reversible/weights-not-intent", "81 exact tensor round trips: coarse view can hide a real change; retained residual recovers it"),
        ("ext:jq-binding-sensitivity", "keeping only the enclosing binding link cuts jq lexical reach from 48 to 3"),
    ]
    for h, what in claims:
        S.append(h, [], ["external", "unverified"], {"claim": what, "source": "Chris 2026-11-20T10:00Z timeline; bundle not in project files"})
    for h, ref in [("prior:bennett", "Bennett 1989, time/space trade-offs for reversible computation"),
                   ("prior:revolve", "Griewank & Walther 2000, Revolve optimal checkpointing (ACM TOMS 26)"),
                   ("prior:rr", "O'Callahan et al. 2017, rr record and replay (USENIX ATC)")]:
        S.append(h, [], ["prior-work"], {"ref": ref})

# ------------------------------------------------------------------
# Measurement helpers: each number is a record
# ------------------------------------------------------------------
def meas(S, cand, inp, obj, value, phase, extra=None):
    r = {"value": value}
    if extra: r.update(extra)
    S.append("meas:%s|%s|%s|%s" % (cand, inp, obj, phase), [cand, "input:" + inp, "obj:" + obj],
             ["measurement", "phase:" + phase], r)

def closure_cands(made):
    return [k for k in made if k.startswith("cand:a/")]

def run_closure(S, cands, inputs, phase, repeats=REPEATS):
    for name, tr in inputs.items():
        e = closure.earliest(tr)
        S.append("input:" + name, [], ["input", "trace", "phase:" + phase],
                 {"records": len(tr), "sha256": traces.digest(tr), "derived": len(e)})
        for k in cands:
            c = made_components(k)
            def once():
                x = closure.make(c["trigger"], c["dedup"], c["check"] if c["check"] != "-" else "short")
                outs = [x.append(rec) for rec in tr]
                return x, outs
            (x, outs), w = timed(once, repeats)
            ok = all(e.get(t) == i for i, new in enumerate(outs) for t in new) and x.D == set(e)
            pk = peak(once)
            meas(S, k, name, "correct_every_prefix", ok, phase)
            meas(S, k, name, "premise_ops", x.ops, phase)
            meas(S, k, name, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"], "runs": w["runs"]})
            meas(S, k, name, "peak_kib", pk, phase)
            print(phase, name, k, ok, x.ops, round(w["median"], 2), pk, flush=True)

_COMP = {}
def made_components(k):
    return _COMP[k]

# ---------------- decision data ----------------
def campaign_inputs(nums):
    out = {}
    for n in nums:
        p = os.path.join(EYES, "campaign-%d" % n, "raw.jsonl")
        out[n] = (traces.campaign(p), sha(p))
    return out

def run_vectors(rows):
    """Admitted per-run cold vectors: verified, driver not disqualified."""
    items = []
    for r in rows:
        if r["mode"] != "cold" or not r.get("verified") or r["driver"] in traces.DRIVERS_DISQUALIFIED:
            continue
        items.append((len(items), (round(r["wall_ms"] * 1000), round(r.get("cpu_ms", 0) * 1000),
                                   r.get("peak_tree_kib", 0), r.get("maxrss_kib", 0))))
    return items

def exact_front(items):
    return {i for i, a in items if not any(b != a and all(x <= y for x, y in zip(b, a)) for _, b in items)}

def joint_instances(rows, limit=100_000):
    opts = traces.options(rows)
    tasks = sorted({o["task"] for o in opts})
    by = {t: [o["cost"] for o in opts if o["task"] == t and not o["disqualified"]] for t in tasks}
    out = []
    for m in range(2, len(tasks) + 1):
        fs = [by[t] for t in tasks[:m]]
        size = 1
        for f in fs: size *= len(f)
        out.append(("tasks%d" % m, fs, size, size <= limit))
    return out

def run_decisions(S, made, camps, phase, repeats=REPEATS, only=None):
    keep = lambda k: only is None or k in only or any(o.startswith(k + "/") for o in only)
    fam = lambda f: [k for k in made if k.startswith("cand:%s/" % f) and keep(k)]
    sel_records = {}
    for n, (rows, h) in camps.items():
        cid = "campaign-%d" % n
        S.append("input:" + cid, [], ["input", "decision-data", "phase:" + phase], {"sha256": h, "rows": len(rows)})
        # (b1) static front over per-run vectors
        items = run_vectors(rows)
        ref = exact_front(items)
        for k in fam("b1"):
            how = made[k]["front"]
            def once():
                ops = decide.Ops()
                if how == "pairwise": f = decide.front_pairwise(items, ops)
                elif how == "sortfilter": f = decide.front_sortfilter(items, ops)
                else:
                    a = decide.Archive()
                    for i, v in items: a.insert(i, v, ops)
                    f = set(a.m)
                return f, ops.n
            (f, nops), w = timed(once, repeats)
            meas(S, k, cid, "correct", f == ref, phase)
            meas(S, k, cid, "dominance_tests", nops, phase)
            meas(S, k, cid, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"]})
        # (d) incremental front after every append
        refs = []
        for j in range(1, len(items) + 1):
            refs.append(exact_front(items[:j]))
        for k in fam("d"):
            how = made[k]["rescoring"]
            def once():
                ops = decide.Ops(); fronts = []
                if how == "archive":
                    a = decide.Archive()
                    for i, v in items:
                        a.insert(i, v, ops); fronts.append(set(a.m))
                else:
                    for j in range(1, len(items) + 1):
                        fn = decide.front_sortfilter if how == "cold-sortfilter" else decide.front_pairwise
                        fronts.append(fn(items[:j], ops))
                return fronts, ops.n
            (fronts, nops), w = timed(once, repeats)
            meas(S, k, cid, "correct_every_prefix", fronts == refs, phase)
            meas(S, k, cid, "dominance_tests", nops, phase)
            meas(S, k, cid, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"]})
        # (b2) joint plans
        for iname, fs, size, brute_ok in joint_instances(rows):
            inp = "%s/%s" % (cid, iname)
            results = {}
            for k in fam("b2"):
                c = made[k]
                if c["joint"] == "brute" and not brute_ok:
                    continue
                def once():
                    ops = decide.Ops()
                    if c["joint"] == "brute": f = decide.plans_brute(fs, ops, prune=c["prune"] == "on")
                    else: f = decide.plans_fold(fs, ops, prune=c["prune"] == "on")
                    return f, ops.n
                (f, nops), w = timed(once, repeats if size <= 20000 else 1)
                pk = peak(once) if size <= 20000 else None
                results[k] = (f, nops, w, pk)
            refset = results.get("cand:b2/joint=brute,prune=off", (None,))[0]
            if refset is None:
                vals = [r[0] for r in results.values()]
                refset = vals[0] if all(v == vals[0] for v in vals) else None
                basis = "cross-agreement"
            else:
                basis = "brute"
            for k, (f, nops, w, pk) in results.items():
                meas(S, k, inp, "correct", f == refset, phase, {"basis": basis, "plans": size, "front": len(f)})
                meas(S, k, inp, "ops", nops, phase)
                meas(S, k, inp, "wall_ms", round(w["median"], 3), phase, {"p25": w["p25"], "p75": w["p75"]})
                if pk is not None:
                    meas(S, k, inp, "peak_kib", pk, phase)
            if not brute_ok or size > 5000:
                continue
            # (b3) selection, (e) weights, (c) stop rules on this instance
            plans = []
            for combo in itertools.product(*fs):
                plans.append((len(plans), tuple(sum(x) for x in zip(*combo))))
            front = exact_front(plans)
            fops = decide.Ops(); decide.front_sortfilter(plans, fops)
            fitems = [(i, v) for i, v in plans if i in front]
            frame = decide.normalize([v for _, v in plans])
            d = len(plans[0][1])
            grid = decide.simplex(d, 10)
            for k in fam("b3"):
                c = made[k]
                pool = plans if c["scope"] == "direct" else fitems
                params = (decide.eps_grid(d, 10) if c["select"] == "eps"
                          else list(itertools.permutations(range(d))) if c["select"] == "lex" else grid)
                ops = decide.Ops(); picks = []
                for w in params:
                    p = decide.pick(c["select"], pool, w, ops, frame)
                    if p is not None: picks.append(p)
                evals = ops.n + (fops.n if c["scope"] == "frontfirst" else 0)  # front cost charged
                onf = sum(1 for p in picks if p in front) / max(len(picks), 1)
                cov = len({p for p in picks if p in front}) / len(front)
                meas(S, k, inp, "pick_on_front_rate", round(onf, 4), phase, {"picks": len(picks), "params": len(params)})
                meas(S, k, inp, "front_coverage_on_grid", round(cov, 4), phase, {"front": len(front)})
                meas(S, k, inp, "evaluations", evals, phase)
            weights_meta(S, inp, fitems, frame, d, phase, only)
            parts = decide.plan_score_parts(fs, [1 / d] * d)
            opt = min(sum(parts[i][c] for i, c in enumerate(combo))
                      for combo in itertools.product(*[range(len(p)) for p in parts]))
            for k in fam("c"):
                rule = made[k]["stop"]
                runs = [("threshold", dl) for dl in (0.05, 0.1, 0.2)] if rule == "threshold" else [(rule, None)]
                for rname, dl in runs:
                    if only is not None and dl is not None and "%s/delta=%s" % (k, dl) not in only:
                        continue
                    ops = decide.Ops()
                    if rname == "bestfirst": res = decide.stop_bestfirst(parts, ops)
                    else: res = decide.stop_stream(parts, rname, dl, ops)
                    kk = k if dl is None else "%s/delta=%s" % (k, dl)
                    if dl is not None and not S.by_head(kk):
                        S.append(kk, [k, "param:delta=%s" % dl], ["candidate", "family:c", "generated:parameter"], {"delta": dl})
                    meas(S, kk, inp, "regret", round(res[1] - opt, 9), phase)
                    meas(S, kk, inp, "examined_ops", ops.n, phase, {"plans_examined": res[2], "plans": size})
                    meas(S, kk, inp, "certified", res[3], phase)
        print(phase, cid, "decisions done", flush=True)

def supported_set(fitems, frame, d, steps=60, lo=1):
    ops = decide.Ops(); out = set()
    for w in decide.simplex(d, steps, lo):
        out.add(decide.pick("ws", fitems, w, ops, frame))
    return out

SCALS = [("ws", 10), ("ws", 20), ("ch", 10), ("ch", 20), ("ach", 10), ("ach", 20), ("eps", 10), ("lex", None), ("ch", "solved"), ("ach", "solved")]

def weights_meta(S, inp, fitems, frame, d, phase, only=None):
    sup = supported_set(fitems, frame, d)
    unsup = {i for i, _ in fitems} - sup
    # added after the smoke run, reported only (never selects): nonnegative weights, zeros allowed
    unsup0 = {i for i, _ in fitems} - supported_set(fitems, frame, d, 60, 0)
    for rule, par in SCALS:
        k = "cand:e/%s,params=%s" % (rule, par)
        if only is not None and k not in only:
            continue
        if not S.by_head(k):
            S.append(k, ["comp:b3/select=%s" % rule, "param:%s" % par], ["candidate", "family:e", "generated:product"], {})
        ops = decide.Ops(); reached = set()
        if par == "solved":
            for i, v in fitems:
                reached.add(decide.pick(rule, fitems, decide.solved_weights(v, frame), ops, frame))
        elif rule == "eps":
            for w in decide.eps_grid(d, par):
                p = decide.pick("eps", fitems, w, ops, frame)
                if p is not None: reached.add(p)
        elif rule == "lex":
            for w in itertools.permutations(range(d)): reached.add(decide.pick("lex", fitems, w, ops, frame))
        else:
            for w in decide.simplex(d, par): reached.add(decide.pick(rule, fitems, w, ops, frame))
        meas(S, k, inp, "coverage", round(len(reached) / len(fitems), 4), phase, {"front": len(fitems), "reached": len(reached)})
        meas(S, k, inp, "unsupported_reached", len(reached & unsup), phase, {"unsupported": len(unsup)})
        meas(S, k, inp, "unsupported_reached_nonneg_reported_only", len(reached & unsup0), phase, {"unsupported": len(unsup0)})
        meas(S, k, inp, "evaluations", ops.n, phase)

# ---------------- (f) binding resolution ----------------
def run_binding(S, made, idol_lib, phase):
    defs = {}
    for lib in sorted(os.listdir(os.path.join(idol_lib, "graphs"))):
        p = os.path.join(idol_lib, "graphs", lib, "graph.json")
        if not os.path.isfile(p): continue
        for n in json.load(open(p))["nodes"]:
            if n["kind"] == "definition": defs[n["id"]] = n
    S.append("input:v2-definitions", [], ["input", "phase:" + phase], {"definitions": len(defs), "commit": git_head(idol_lib)})
    def chain(d):
        out, x = [], defs[d]["scope"]["enclosing"]
        while x:
            out.append(x); x = defs[x]["scope"]["enclosing"] if x in defs else None
        return out
    target = [d for d, n in defs.items() if n["library"] == "jq" and n["name"] == "shape" and n["scope"]["enclosing"] is None]
    for k in [k for k in made if k.startswith("cand:f/")]:
        how = made[k]["resolver"]
        edges, amb, unres, unsound = {}, 0, 0, 0
        for d, n in defs.items():
            ch = set(chain(d)) | {d}
            es = set()
            if how == "enclosing":
                if n["scope"]["enclosing"]: es.add(n["scope"]["enclosing"])
                edges[d] = es; continue
            for ref in n.get("references", []):
                cs = [c for c in ref["candidates"] if c in defs]
                if how in ("visible", "nearest"):
                    cs = [c for c in cs if defs[c]["scope"]["enclosing"] is None or defs[c]["scope"]["enclosing"] in ch]
                if how == "nearest" and cs:
                    depth = lambda c: len(chain(c))
                    best = max(depth(c) for c in cs)
                    cs = [c for c in cs if depth(c) == best]
                    same = [c for c in cs if defs[c]["source"]["path"] == n["source"]["path"]]
                    cs = same or cs
                if not cs: unres += 1
                if len(cs) > 1: amb += 1
                for c in cs:
                    if defs[c]["scope"]["enclosing"] is not None and defs[c]["scope"]["enclosing"] not in ch:
                        unsound += 1
                    es.add(c)
            edges[d] = es
        # reach of jq shape: definitions that depend on it transitively (reported only)
        rev = {}
        for d, es in edges.items():
            for c in es: rev.setdefault(c, set()).add(d)
        seen, stack = set(), list(target)
        while stack:
            x = stack.pop()
            for y in rev.get(x, ()):
                if y not in seen: seen.add(y); stack.append(y)
        meas(S, k, "v2-definitions", "lexically_unsound_edges", unsound, phase)
        meas(S, k, "v2-definitions", "ambiguous_refs", amb, phase)
        meas(S, k, "v2-definitions", "unresolved_refs", unres, phase)
        meas(S, k, "v2-definitions", "jq_shape_reach_reported_only", len(seen), phase)
        print(phase, k, unsound, amb, unres, len(seen), flush=True)

def git_head(path):
    import subprocess
    return subprocess.run(["git", "-C", path, "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()

def main():
    phase, out = sys.argv[1], sys.argv[2]
    os.makedirs(out, exist_ok=True)
    S = Space(os.path.join(out, "space.jsonl"))
    if phase == "dev":
        assert not S.recs, "dev phase starts a fresh log"
        S.append("objectives", [], ["declared"], {"sha256": sha(os.path.join(HERE, "OBJECTIVES.json"))})
        axes = components(S)
        made = generate(S, axes)
        _COMP.update(made)
        external(S)
        run_binding(S, made, sys.argv[3], "dev")
        if not os.environ.get("SKIP_CLOSURE"):
            run_closure(S, closure_cands(made), traces.dev_closure(), "dev")
        run_decisions(S, made, campaign_inputs([1, 2, 3, 4]), "dev")
    print("records", len(S.recs), "head", S.prev)

if __name__ == "__main__":
    main()
