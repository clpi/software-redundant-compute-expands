# Round 2 of the semantic axes (AXES.json round_2, declared and pushed
# before this file ran). Appends to the same hash-chained log.
#   python3 round2.py out dev                    every ax-a candidate, new ones included
#   python3 axes_select.py out/space.jsonl r2-dev
#   python3 round2.py out heldout IDOL_LIB       frozen survivors + controls + current
import importlib.util, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE); sys.path.insert(0, os.path.join(HERE, "..", "algorithm-search"))
import axes_run as A
import traces
from space import Space

NEW_LIBS = ("blake2b", "flatbuf", "protobuf", "toml")
FRESH_REV = "f8a45b4"

def alias(tr):
    """T+alias: before the first producing record of each head with
    premises, an alias record whose extra premise nothing produces."""
    heads = {h for _, _, _, _, h in tr}
    top = 1 + max(max([h] + list(ps)) for _, _, _, ps, h in tr)
    seen, out = set(), []
    for rec in tr:
        _, lv, cs, ps, h = rec
        if ps and h not in seen:
            out.append((len(out), lv, cs, list(ps) + [top + len(out)], h))
        seen.add(h)
        out.append((len(out), lv, cs, list(ps), h))
    assert all(top + i not in heads for i in range(len(out)))
    return out

def with_alias(ins):
    out = {}
    for name, tr in ins.items():
        out[name] = tr
        out[name + "+alias"] = alias(tr)
    return out

def load_made(S):
    made = {}
    for r in S.with_color("candidate"):
        if "components" in r["receipt"]:
            made[r["head"]] = r["receipt"]["components"]
        elif "control" in r["colors"]:
            made[r["head"]] = {"control": r["head"].split("=")[1]}
    return made

def generate2(S, made):
    S.append("axes-round-2", ["axes"], ["declared"], {"sha256": A.sha(os.path.join(HERE, "AXES.json")), "commit": "49c9ad4"})
    S.append("comp:ax-a/merge=adaptive", [], ["component", "family:ax-a"], {})
    S.append("rule:ax-a rounds has no adaptive merge", [], ["constraint"], {"why": "a round-based state has no pending-waiter structure to estimate; adaptive collapses to propagate"})
    ax = A.AXES["a"]
    for eng in ax["engine"]:
        for undo in ax["undo"]:
            for wit in ax["witness"]:
                c = {"engine": eng, "undo": undo, "witness": wit, "merge": "adaptive"}
                if eng == "rounds":
                    if undo == "journal": c["undo"] = "none"
                    c["merge"] = "propagate"
                key = "cand:ax-a/" + ",".join("%s=%s" % (n, c[n]) for n in ("engine", "undo", "witness", "merge"))
                comps = ["comp:ax-a/%s=%s" % (n, v) for n, v in (("engine", eng), ("undo", undo), ("witness", wit), ("merge", "adaptive"))]
                colors = ["candidate", "family:ax-a", "generated:product", "round:2"] + (["collapsed"] if key in made else [])
                S.append(key, comps, colors, {"components": c})
                made[key] = c
    return made

def fresh(idol_lib):
    """fresh-refs and fresh-v2 from the four library homes added on
    idol-lib master after every earlier run, using idol-lib's own
    graphs/build.py over a locally hashed manifest."""
    wt = tempfile.mkdtemp(prefix="idol-lib-fresh-")
    subprocess.run(["git", "-C", idol_lib, "worktree", "add", "--detach", "-q", wt, FRESH_REV], check=True)
    try:
        commit = subprocess.check_output(["git", "-C", wt, "rev-parse", "HEAD"], text=True).strip()
        tree = subprocess.check_output(["git", "-C", wt, "rev-parse", "HEAD^{tree}"], text=True).strip()
        spec = importlib.util.spec_from_file_location("idol_build", os.path.join(wt, "graphs", "build.py"))
        b = importlib.util.module_from_spec(spec); spec.loader.exec_module(b)
        from pathlib import Path
        root = Path(wt)
        files = []
        for p in b.inventory(root, NEW_LIBS):
            data = (root / p).read_bytes()
            files.append({"path": p, "bytes": len(data), "sha256": b.sha256(data), "git_blob_sha1": b.blobsha(data), "role": b.role(p)})
        manifest = {"repository": "clpi/idol-lib", "commit": commit, "tree": tree, "files": files}
        graphs = {lib: b.build_graph(root, lib, manifest) for lib in NEW_LIBS}
    finally:
        subprocess.run(["git", "-C", idol_lib, "worktree", "remove", "--force", wt], check=False)
    terms, refs, v2 = {}, [], []
    def t(x):
        if x not in terms: terms[x] = len(terms)
        return terms[x]
    t2 = {}
    def u(x):
        if x not in t2: t2[x] = len(t2)
        return t2[x]
    for lib in NEW_LIBS:
        g = graphs[lib]
        for n in g["nodes"]:
            if n["kind"] == "definition":
                ps = []
                for ref in n.get("references", []):
                    ps += [t(c) for c in ref["candidates"]]
                refs.append((len(refs), 0, [2], ps, t(n["id"])))
        heads = {e["conclusion"] for e in g["edges"]}
        for n in g["nodes"]:
            if n["id"] not in heads:
                v2.append((len(v2), 0, [2], [], u(n["id"])))
        for e in g["edges"]:
            v2.append((len(v2), 0, [2], [u(p) for p in e["premises"]], u(e["conclusion"])))
    return {"fresh-refs": refs, "fresh-v2": v2}, {"commit": commit, "tree": tree, "files": len(files),
            "per_library_nodes": {l: len(graphs[l]["nodes"]) for l in NEW_LIBS}}

def main():
    out, phase = sys.argv[1], sys.argv[2]
    S = Space(os.path.join(out, "space.jsonl"))
    made = load_made(S)
    if phase == "dev":
        assert not [r for r in S.recs if r["head"] == "axes-round-2"], "round 2 dev already ran"
        made = generate2(S, made)
        ins = with_alias(traces.dev_closure())
        A.run_closure(S, made, ins, "r2-dev")
    elif phase == "dev-resume":
        # the dev run was stopped by the session's background time limit
        # between two candidates; record that, then measure only the
        # (candidate, input) pairs that have no complete set of axes yet
        done = {(r["premises"][0], r["premises"][1]) for r in S.with_color("phase:r2-dev") if r["head"].endswith("|robustness|r2-dev")}
        ins = with_alias(traces.dev_closure())
        todo = {n: [k for k in made if k.startswith("cand:ax-a/") and (k, "input:ax/" + n) not in done] for n in ins}
        S.append("attempt:r2-dev-1", [], ["attempt", "interrupted"], {"why": "background time limit of the session stopped the run between candidates; no partial candidate", "remaining": {n: len(v) for n, v in todo.items()}})
        for n, ks in todo.items():
            if ks:
                A.run_closure(S, made, {n: ins[n]}, "r2-dev", only=set(ks))
    elif phase in ("heldout", "heldout-resume"):
        fr = [r for r in S.with_color("downselect") if r["head"] == "downselect:ax-r2-dev"]
        assert fr, "run axes_select.py out/space.jsonl r2-dev first"
        idol_lib = sys.argv[3]
        from axes_select import CURRENT
        keep = set(fr[-1]["receipt"]["survivors"]) | {k for k in made if k.startswith("cand:ax-a/control=")} | set(CURRENT["ax-a"])
        ho = traces.heldout_closure(idol_lib)
        fr2, meta = fresh(idol_lib)
        ho.update(fr2)
        ins = with_alias(ho)
        if phase == "heldout-resume":
            # stopped by the session's background time limit; finish only the
            # (candidate, input) pairs with no complete set of axes yet
            done = {(r["premises"][0], r["premises"][1]) for r in S.with_color("phase:r2-heldout") if r["head"].endswith("|robustness|r2-heldout")}
            built = {r["head"][len("heldout-built:ax/"):]: r["receipt"]["sha256"] for r in S.recs if r["head"].startswith("heldout-built:ax/") and "phase:r2-heldout" in r["colors"]}
            assert all(built.get(n, traces.digest(tr)) == traces.digest(tr) for n, tr in ins.items()), "rebuilt held-out traces differ"
            todo = {n: sorted(k for k in keep if (k, "input:ax/" + n) not in done) for n in ins}
            S.append("attempt:r2-heldout-1", [], ["attempt", "interrupted"], {"remaining": {n: len(v) for n, v in todo.items()}})
            for n, ks in todo.items():
                if ks:
                    if n not in built:
                        S.append("heldout-built:ax/" + n, [], ["heldout", "phase:r2-heldout"], {"records": len(ins[n]), "sha256": traces.digest(ins[n])})
                    A.run_closure(S, made, {n: ins[n]}, "r2-heldout", only=set(ks))
            print("records", len(S.recs), "head", S.prev); return
        for name, tr in ins.items():
            S.append("heldout-built:ax/" + name, [], ["heldout", "phase:r2-heldout"], dict({"records": len(tr), "sha256": traces.digest(tr)}, **(meta if name.startswith("fresh") else {})))
        A.run_closure(S, made, ins, "r2-heldout", only=keep)
    print("records", len(S.recs), "head", S.prev)

if __name__ == "__main__":
    main()
