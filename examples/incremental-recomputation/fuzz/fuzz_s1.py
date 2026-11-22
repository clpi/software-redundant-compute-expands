#!/usr/bin/env python3
"""Randomized differential test: frontier.Frontier and metasearch.MetaEngine
against independent from-scratch references, after every operation of long
random sequences (joins, re-joins, moves, withdrawals; small integer vectors
so ties and duplicate vectors occur). usage: fuzz_s1.py [meta.py|-] [seeds] [steps]
Without meta.py (or with -) only the frontier engine runs; the meta-search
engine is loaded from beside this checkout or from <meta.py dir>/incremental."""
import os, random, sys
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import frontier as F
MS = None


def fuzz_frontier(seed, steps, dims):
    rng = random.Random(seed)
    sense = tuple(rng.choice((-1, 1)) for _ in range(dims))
    eng, cur = F.Frontier(sense), {}
    names = ["i%d" % k for k in range(12)]
    for step in range(steps):
        op = rng.random()
        n = rng.choice(names)
        if op < 0.55 or not cur:
            v = tuple(rng.randint(0, 3) for _ in range(dims))
            eng.join(n, v); cur[n] = v
        elif op < 0.7 and n in cur:
            eng.join(n, cur[n])  # unchanged re-join: carry
        elif n in cur:
            eng.withdraw(n); del cur[n]
        ref, _ = F.naive_frontier(cur, sense)
        if eng.frontier() != sorted(ref) or not eng.recheck_premises():
            return "frontier seed %d step %d: engine %s ref %s" % (seed, step, eng.frontier(), sorted(ref))
    return None


def fuzz_meta(meta, seed, steps):
    rng = random.Random(seed)
    cfgs = meta.configurations()
    e = MS.MetaEngine(meta)
    pending = [(n, list(c), m) for n, c, m in meta.INSTANCES]
    rng.shuffle(pending)
    cur = []
    for _ in range(rng.randint(1, len(pending))):   # some instances before the configurations
        n, c, m = pending.pop(0)
        cur.append((n, c, m)); e.add_instance(n, list(c), m)
    for cfg in cfgs:
        e.join_config(cfg)
    for step in range(steps):
        if pending and rng.random() < 0.05:          # the rest join later, as instance joins
            n, c, m = pending.pop(0)
            cur.append((n, c, m)); e.add_instance(n, list(c), m)
        idx = rng.randrange(len(cur))
        names = [c[0] for c in cur[idx][1]]
        if rng.random() < 0.7:
            name = rng.choice(names)          # move an existing candidate
        else:
            name = "n%d_%d" % (seed, step)    # a new candidate
        x, y = rng.randint(0, 13), rng.randint(0, 13)
        if rng.random() < 0.15:               # duplicate another candidate's vector
            o = rng.choice(cur[idx][1]); x, y = o[1], o[2]
        cands = [c for c in cur[idx][1] if c[0] != name] + [(name, x, y)]
        cur[idx] = (cur[idx][0], cands, cur[idx][2])
        e.join_candidate(idx, name, x, y)
        fronts = [meta.frontier_of(c) for _n, c, _m in cur]
        if sorted(e.inst_front[idx].frontier()) != sorted(c[0] for c in fronts[idx]):
            return "meta seed %d step %d: instance frontier differs" % (seed, step)
        ref_meas = {}
        for cfg in cfgs:
            miss = tie = 0
            picks = []
            for i, front in enumerate(fronts):
                pick, win = meta.induced(cfg[0], cfg[1], front)
                tie += len(win) - 1
                miss += pick != cur[i][2]
                picks.append(pick if pick is not None else "tie " + "/".join(win))
            if e.picks(cfg) != picks:
                return "meta seed %d step %d: selection differs for %s: %s vs %s" % (
                    seed, step, meta.label(*cfg), e.picks(cfg), picks)
            ref_meas[cfg] = (miss, tie, meta.simplicity(*cfg), meta.FAMILY_RANK[cfg[0]])
            if e.measures[cfg] != ref_meas[cfg]:
                return "meta seed %d step %d: measures differ for %s" % (seed, step, meta.label(*cfg))
        ref_front, _ = F.naive_frontier(ref_meas, (-1, -1, -1, -1))
        if sorted(e.meta_front.frontier()) != sorted(ref_front):
            return "meta seed %d step %d: meta-frontier differs" % (seed, step)
    return None


def main():
    global MS
    meta_path = sys.argv[1] if len(sys.argv) > 1 and sys.argv[1] != "-" else None
    seeds = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    steps = int(sys.argv[3]) if len(sys.argv) > 3 else 200
    bad = []
    for s in range(seeds):
        for d in (1, 2, 3):
            r = fuzz_frontier(s, steps, d)
            if r: bad.append(r)
    line = "frontier: %d sequences x %d ops x dims 1-3" % (seeds, steps)
    if meta_path:
        sys.path.append(os.path.join(os.path.dirname(os.path.abspath(meta_path)), "incremental"))
        import metasearch
        MS = metasearch
        meta = MS.load_meta(meta_path)
        for s in range(seeds // 4):
            r = fuzz_meta(meta, s, steps // 2)
            if r: bad.append(r)
        line += "; meta: %d sequences x %d ops" % (seeds // 4, steps // 2)
    print(line)
    for b in bad[:10]:
        print("DISAGREE", b)
    print("FUZZ s1: %s (%d disagreements)" % ("PASS" if not bad else "FAIL", len(bad)))
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
