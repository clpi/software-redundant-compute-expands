#!/usr/bin/env python3
"""Standing gate: every incremental engine against its from-scratch checker.

usage:
  gate.py all <reversible checkout> <prlm checkout> <hma checkout> [counts.json]
  gate.py s1 [points.json]      system 1, candidate-space frontier (fixture ships
                                with the candidate-space home only)
  gate.py meta <meta.py>        system 1, the reversible repo's meta-search
  gate.py s2 <harness/run.py>   system 2, PRLM certified decoder
  gate.py s3 <solver dir>       system 3, HMA solver

Prints one PASS/FAIL line per check and the counts behind it, then GATE:
PASS or GATE: FAIL (exit 1). Counts are the claims; the two wall-clock
lines are single runs on this machine and indicative only.

Each engine has a mutant that breaks its cone rule in one place; the
gate must catch every mutant (a mutant that agrees is a FAIL: the
checks would have no teeth).
"""
from __future__ import annotations

import json
import os
import random
import sys
import time
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

F = MS = SY = AX = None  # imported per section, so each home carries only its engine


def home(path):
    """Make an engine's own home importable. Each home repo carries its engine in
    an incremental/ directory next to the checker input: meta.py and harness/run.py
    have it beside them, the HMA solver dir has it inside. Appended, so a module
    next to this gate (the work home carries all four) still wins."""
    d = path if os.path.isdir(path) else os.path.dirname(os.path.abspath(path))
    inc = os.path.join(d, "incremental")
    if os.path.isdir(inc) and inc not in sys.path:
        sys.path.append(inc)


def need(*names):
    g = globals()
    for n, mod in (("F", "frontier"), ("MS", "metasearch"), ("SY", "synthesis"), ("AX", "axis")):
        if n in names and g[n] is None:
            g[n] = __import__(mod)

RESULTS = []
COUNTS = {}


def check(ok, text):
    RESULTS.append(bool(ok))
    print(("PASS " if ok else "FAIL ") + text)


# ---------------------------------------------------------------- system 1

def s1(points_path):
    need("F")
    doc = json.load(open(points_path))
    for key in sorted(doc["instances"]):
        pts = doc["instances"][key]["points"]
        sense = (-1,) * len(doc["instances"][key]["columns"])
        names = sorted(pts)
        eng = F.Frontier(sense)
        per_join = []
        prefix_ok = True
        for i, n in enumerate(names):
            before = eng.evals
            eng.join(n, pts[n])
            per_join.append(eng.evals - before)
            ref, _ = F.naive_frontier({m: pts[m] for m in names[:i + 1]}, sense)
            prefix_ok &= eng.frontier() == ref
        n = len(names)
        ref, full = F.naive_frontier(pts, sense)
        predicted = [2 * i for i in range(n)]
        check(prefix_ok and eng.frontier() == ref,
              "s1 %s: frontier agrees with the from-scratch checker at all %d append prefixes (frontier %d)"
              % (key, n, len(ref)))
        check(per_join == predicted and full == n * (n - 1),
              "s1 %s: join k costs 2(k-1) ordered evaluations (last join %d, build %d) vs %d for one full recompute"
              % (key, per_join[-1], sum(per_join[:-1]), full))
        COUNTS["s1 " + key] = {"items": n, "frontier": len(ref), "last_join": per_join[-1],
                              "build_first_n_minus_1": sum(per_join[:-1]), "full": full}
        # order independence
        rng = random.Random(7)
        perm = names[:]
        rng.shuffle(perm)
        e2 = F.Frontier(sense)
        for m in perm:
            e2.join(m, pts[m])
        check(e2.frontier() == eng.frontier() and e2.dominators == eng.dominators,
              "s1 %s: a shuffled join order gives the same frontier and the same dominance matrix" % key)
        # unchanged re-join
        before = eng.evals
        eng.join(names[0], pts[names[0]])
        check(eng.evals == before, "s1 %s: unchanged re-join carries at 0 evaluations" % key)
        # withdraw every frontier member, one at a time, with no evaluation
        live = dict(pts)
        wd_ok, wd_evals = True, 0
        for m in list(ref)[:max(0, min(len(ref), n - 2))]:
            before = eng.evals
            eng.withdraw(m)
            wd_evals += eng.evals - before
            del live[m]
            wd_ok &= eng.frontier() == F.naive_frontier(live, sense)[0]
        check(wd_ok and wd_evals == 0,
              "s1 %s: withdrawing %d frontier members one by one re-admits exactly the right items at 0 evaluations"
              % (key, min(len(ref), n - 2)))
        # score change named as withdrawal plus join
        m = names[-1] if names[-1] in live else sorted(live)[0]
        newv = [x - 1 for x in live[m]]
        before = eng.evals
        eng.join(m, newv)
        live[m] = newv
        check(eng.frontier() == F.naive_frontier(live, sense)[0]
              and eng.evals - before == 2 * (len(live) - 1)
              and eng.log[-2][0] == "withdraw:score change",
              "s1 %s: a score change is logged as withdrawal plus join and agrees with the checker" % key)
        check(eng.recheck_premises(), "s1 %s: every carried premise hash matches its vector" % key)
    # mutant: reverse direction never evaluated
    caught = False
    for key in sorted(doc["instances"]):
        pts = doc["instances"][key]["points"]
        sense = (-1,) * len(doc["instances"][key]["columns"])
        mut = F.Frontier(sense, one_direction_mutant=True)
        for n in sorted(pts):
            mut.join(n, pts[n])
        caught |= mut.frontier() != F.naive_frontier(pts, sense)[0]
    check(caught, "s1 mutant (reverse dominance never evaluated) is caught by the checker")


# ---------------------------------------------------- system 1, meta-search

def s1_meta(meta_path):
    home(meta_path)
    need("F", "MS")
    meta = MS.load_meta(meta_path)
    cfgs = meta.configurations()
    eng = MS.MetaEngine(meta)
    for n, c, mid in meta.INSTANCES:
        eng.add_instance(n, c, mid)
    for cfg in cfgs:
        eng.join_config(cfg)
    lab = lambda c: meta.label(*c)

    def agree(instances, configs):
        ref, _rc, text = MS.checker(meta, instances, configs)
        mine = sorted(lab(c) for c in eng.meta_front.frontier())
        rows_ok = all(("%-38s %-22s %-22s %-22s %s" % ((lab(c),) + tuple(eng.picks(c)) + (eng.measures[c],)))
                      in text for c in configs)
        return mine == ref and rows_ok, len(ref)

    ok, nf = agree(meta.INSTANCES, cfgs)
    build = eng.meta_front.evals
    check(ok and build == 39 * 38,
          "meta: 39 configurations joined; meta-frontier (%d) and every configuration row agree with meta.py; "
          "build cost %d meta evaluations, equal to one full recompute (39 x 38): building by joins saves nothing"
          % (nf, build))
    COUNTS["meta build"] = {"configs": 39, "meta_evals": build, "full": 39 * 38, "frontier": nf}
    # 40th configuration
    new = ("overlay", (4,))
    before_m, before_s = eng.meta_front.evals, eng.score_evals
    eng.join_config(new)
    cfgs40 = cfgs + [new]
    ok, nf = agree(meta.INSTANCES, cfgs40)
    jm, js = eng.meta_front.evals - before_m, eng.score_evals - before_s
    check(ok and jm == 2 * 39,
          "meta: 40th configuration (%s) joins at %d meta evaluations and %d score evaluations vs %d meta "
          "evaluations for a full recompute; agrees with meta.py" % (lab(new), jm, js, 40 * 39))
    COUNTS["meta join config"] = {"meta_evals": jm, "score_evals": js, "full_meta": 40 * 39}
    # dominated instance candidate: frontier unchanged, everything carries
    insts = [(n, list(c), m) for n, c, m in meta.INSTANCES]
    before_m, before_s = eng.meta_front.evals, eng.score_evals
    insts[2][1].append(("stalled", 13, 9))
    full, changed = eng.join_candidate(2, "stalled", 13, 9)
    ok, _ = agree(insts, cfgs40)
    check(ok and full == changed == 0 and eng.score_evals == before_s and eng.meta_front.evals == before_m,
          "meta: a dominated decoding candidate leaves the instance frontier unchanged; 0 selections rescored, "
          "0 meta evaluations; agrees with meta.py")
    # frontier-entering candidate
    before_m, before_s = eng.meta_front.evals, eng.score_evals
    insts[2][1].append(("terse", 3, 8))
    full, changed = eng.join_candidate(2, "terse", 3, 8)
    ok, nf = agree(insts, cfgs40)
    sm, ss = eng.meta_front.evals - before_m, eng.score_evals - before_s
    check(ok, "meta: a frontier-entering decoding candidate (3, 8): %d full rescores, %d score evaluations, "
              "%d configurations changed measures, %d meta evaluations; meta-frontier %d agrees with meta.py"
              % (full, ss, changed, sm, nf))
    COUNTS["meta join candidate"] = {"full_rescores": full, "score_evals": ss, "changed": changed,
                                     "meta_evals": sm, "scratch_score_evals": 40 * sum(
                                         len(meta.frontier_of(c)) for _n, c, _m in insts),
                                     "scratch_meta_evals": 40 * 39}
    # candidate that pushes a winner off the frontier
    before_m, before_s = eng.meta_front.evals, eng.score_evals
    insts[2][1].append(("crisp", 5, 5))
    full, changed = eng.join_candidate(2, "crisp", 5, 5)
    ok, nf = agree(insts, cfgs40)
    check(ok and full > 0, "meta: (5, 5) knocks 'balanced' off the frontier: %d selections rescored in full "
                           "(only those it had won), %d changed measures; agrees with meta.py" % (full, changed))
    # instance joins after configurations: every split of the three instances into
    # "before the configurations" and "after", in every order
    import itertools
    late_ok, late_changes, late_n = True, 0, 0
    for perm in itertools.permutations(range(len(meta.INSTANCES))):
        for k in range(len(perm)):
            e2 = MS.MetaEngine(meta)
            for i in perm[:k]:
                e2.add_instance(*meta.INSTANCES[i])
            for cfg in cfgs:
                e2.join_config(cfg)
            try:
                for i in perm[k:]:
                    late_changes += e2.add_instance(*meta.INSTANCES[i]) or 0
                    late_n += 1
                insts = [meta.INSTANCES[i] for i in perm]
                ref, _rc, text = MS.checker(meta, insts, cfgs)
                mine = sorted(lab(c) for c in e2.meta_front.frontier())
                rows = all(("%-38s %-22s %-22s %-22s %s" % ((lab(c),) + tuple(e2.picks(c)) + (e2.measures[c],)))
                           in text for c in cfgs)
                late_ok &= mine == ref and rows
            except KeyError:
                late_ok = False  # a selection on the late instance was never computed
    check(late_ok, "meta: instances joined after the configurations (every order, every split; %d instance "
                   "joins, %d measure changes re-joined) agree with meta.py in every row and the meta-frontier"
                   % (late_n, late_changes))
    # score changes of candidates already present (withdrawal plus join at the selection level)
    deltas = [(-2, 0), (0, -2), (2, 2), (-3, -3), (5, 0), (-1, 1)]

    def moves(mutant):
        e = MS.MetaEngine(meta, ignore_moved_mutant=mutant)
        for n, c, mid in meta.INSTANCES:
            e.add_instance(n, c, mid)
        for cfg in cfgs:
            e.join_config(cfg)
        cur = [(n, list(c), m) for n, c, m in meta.INSTANCES]
        n_moves = bad = stay = full_n = s_ev = 0
        for idx in range(len(cur)):
            for name, x0, y0 in list(cur[idx][1]):
                for dx, dy in deltas:
                    for (x, y) in ((x0 + dx, y0 + dy), (x0, y0)):
                        cur[idx] = (cur[idx][0], [(n, x, y) if n == name else (n, a, b)
                                                  for n, a, b in cur[idx][1]], cur[idx][2])
                        was = set(e.inst_front[idx].frontier())
                        before = e.score_evals
                        f, _c = e.join_candidate(idx, name, x, y)
                        s_ev += e.score_evals - before
                        full_n += f
                        stay += was == set(e.inst_front[idx].frontier()) and name in was
                        n_moves += 1
                        front = meta.frontier_of(cur[idx][1])
                        for cfg in cfgs:
                            pick, win = meta.induced(cfg[0], cfg[1], front)
                            want = pick if pick is not None else "tie " + "/".join(win)
                            bad += e.picks(cfg)[idx] != want
        ref, _rc, text = MS.checker(meta, cur, cfgs)
        mine = sorted(lab(c) for c in e.meta_front.frontier())
        rows = all(("%-38s %-22s %-22s %-22s %s" % ((lab(c),) + tuple(e.picks(c)) + (e.measures[c],)))
                   in text for c in cfgs)
        return n_moves, bad, stay, full_n, s_ev, mine == ref and rows

    n_moves, bad, stay, full_n, s_ev = moves(False)[:5]
    end_ok = moves(False)[5]
    check(bad == 0 and end_ok,
          "meta: %d score changes of candidates already present (each moved, then restored; %d kept the "
          "frontier set unchanged) agree with meta.induced in every one of 39 selections after every change, "
          "and the end state agrees with meta.py; %d full rescores, %d score evaluations"
          % (n_moves, stay, full_n, s_ev))
    COUNTS["meta score changes"] = {"moves": n_moves, "membership_unchanged": stay, "full_rescores": full_n,
                                    "score_evals": s_ev}
    mbad = moves(True)[1]
    check(mbad > 0, "meta mutant (a member's own score change ignored when frontier membership is unchanged) "
                    "is caught: %d stale selections" % mbad)


# ---------------------------------------------------------------- system 2

def s2(run_py):
    home(run_py)
    need("SY")
    h = SY.load_harness(run_py)
    for seed in (11, 23):
        table = h.build_table(seed)
        queries = h.queries_for(table, seed)
        eng = SY.Engine(h, table, queries)
        eng.build()
        ref, lk = SY.scratch(h, eng.table, eng.keys)
        check(all(eng.verdict(k) == ref[k] for k in eng.keys),
              "s2 seed %d: %d queries (%d distinct): every verdict agrees with the from-scratch decoder "
              "(%d lookups either way)" % (seed, len(queries), len(eng.keys), lk))
        holders = {}
        for k in eng.keys:
            for rk in eng.state[k][1]:
                holders.setdefault(rk, set()).add(k)
        edits = []
        for rk in sorted(holders, key=repr):
            row = dict.get(eng.table, rk)
            if row is None:
                edits.append((rk, None, [(0, Fraction(1))]))
            else:
                edits.append((rk, row, None))  # withdrawal of the row
                for tok, _w in row:
                    for mult in (Fraction(2), Fraction(1, 2), Fraction(3)):
                        edits.append((rk, row, SY.overlay(row, tok, mult)))
        all_ok, scoped_ok, dist = True, True, []
        for rk, orig, new in edits:
            cost = eng.edit(rk, new)
            ref, lk = SY.scratch(h, eng.table, eng.keys)
            all_ok &= all(eng.verdict(k) == ref[k] for k in eng.keys)
            scoped_ok &= set(eng.rederived) == holders[rk] or (new == orig and not eng.rederived)
            dist.append((len(eng.rederived), cost, lk))
            eng.edit(rk, orig)  # revert, itself an edit
            ref, _ = SY.scratch(h, eng.table, eng.keys)
            all_ok &= all(eng.verdict(k) == ref[k] for k in eng.keys)
            # cones can change under an edit; refresh holders after revert
            holders = {}
            for k in eng.keys:
                for r2 in eng.state[k][1]:
                    holders.setdefault(r2, set()).add(k)
        miss_edits = sum(1 for e in edits if e[1] is None)
        del_edits = sum(1 for e in edits if e[2] is None)
        check(all_ok, "s2 seed %d: all %d single-key edits (%d insert a row where a cone saw none, %d withdraw "
                      "a row) and their reverts agree with the from-scratch decoder"
              % (seed, len(edits), miss_edits, del_edits))
        check(scoped_ok, "s2 seed %d: every edit re-derived exactly the queries whose cones hold its key"
              % seed)
        tot_inc = sum(c for _r, c, _l in dist)
        tot_scr = sum(l for _r, _c, l in dist)
        one = [(r, c, l) for r, c, l in dist if r == 1]
        print("     s2 seed %d edit distribution: re-derived per edit min %d max %d mean %.2f of %d; "
              "lookups per edit min %d max %d; total %d vs %d from scratch over the same %d edits"
              % (seed, min(r for r, _c, _l in dist), max(r for r, _c, _l in dist),
                 sum(r for r, _c, _l in dist) / len(dist), len(eng.keys),
                 min(c for _r, c, _l in dist), max(c for _r, c, _l in dist), tot_inc, tot_scr, len(dist)))
        COUNTS["s2 seed %d" % seed] = {
            "queries": len(queries), "distinct": len(eng.keys), "edits": len(edits),
            "missing_row_edits": miss_edits, "rederived_max": max(r for r, _c, _l in dist),
            "rederived_mean": round(sum(r for r, _c, _l in dist) / len(dist), 3),
            "lookups_incremental_total": tot_inc, "lookups_scratch_total": tot_scr,
            "one_rederived_examples": sorted(set(one))[:6]}
        # early cutoff: an edit that writes back the value every cone saw
        rk = sorted(holders, key=lambda k: -len(holders[k]))[0]
        same = dict.get(eng.table, rk)
        cost = eng.edit(rk, list(same) if same is not None else None)
        ref, _ = SY.scratch(h, eng.table, eng.keys)
        check(cost == 0 and not eng.rederived and all(eng.verdict(k) == ref[k] for k in eng.keys),
              "s2 seed %d: an edit at a key %d cones hold that leaves its value unchanged is cut off early "
              "(0 re-derived, 0 lookups) and agrees" % (seed, len(holders[rk])))
        # cone-disjoint control: a key no cone holds
        free = [k for k in table if k not in holders]
        if free:
            row = table[free[0]]
            cost = eng.edit(free[0], SY.overlay(row, row[0][0], Fraction(2)))
            ref, _ = SY.scratch(h, eng.table, eng.keys)
            check(cost == 0 and not eng.rederived and all(eng.verdict(k) == ref[k] for k in eng.keys),
                  "s2 seed %d: an edit at a row no cone holds re-derives 0 queries at 0 lookups and agrees"
                  % seed)
            eng.edit(free[0], row)
        # chained edits, never reverted
        rng = random.Random(seed + 9)
        chain_ok = True
        for _ in range(60):
            keys = sorted(dict.keys(eng.table), key=repr)
            rk = rng.choice(keys)
            row = dict.get(eng.table, rk)
            tok = rng.choice(row)[0]
            eng.edit(rk, SY.overlay(row, tok, rng.choice([Fraction(2), Fraction(1, 2), Fraction(3)])))
            ref, _ = SY.scratch(h, eng.table, eng.keys)
            chain_ok &= all(eng.verdict(k) == ref[k] for k in eng.keys)
        check(chain_ok, "s2 seed %d: 60 chained edits with carried state never reset agree after every edit"
              % seed)
    # resume: re-derivation restarts at the first read of the edited key
    for seed in (11, 23):
        table = h.build_table(seed)
        queries = h.queries_for(table, seed)
        res = SY.ResumeEngine(h, table, queries)
        res.build()
        whole = SY.Engine(h, table, queries)
        whole.build()
        ref, lk = SY.scratch(h, res.table, res.keys)
        ok = all(res.verdict(k) == ref[k] for k in res.keys)
        holders = {}
        for k in res.keys:
            for rk in res.state[k][1]:
                holders.setdefault(rk, set()).add(k)
        r_tot = w_tot = s_tot = n = 0
        same_set = True
        for rk in sorted(holders, key=repr):
            row = dict.get(res.table, rk)
            news = ([None] + [SY.overlay(row, tok, m) for tok, _w in row
                              for m in (Fraction(2), Fraction(1, 2), Fraction(3))]
                    if row is not None else [[(0, Fraction(1))]])
            for new in news:
                cr, cw = res.edit(rk, new), whole.edit(rk, new)
                ref, ls = SY.scratch(h, res.table, res.keys)
                ok &= all(res.verdict(k) == ref[k] for k in res.keys)
                same_set &= set(res.rederived) == set(whole.rederived)
                r_tot, w_tot, s_tot, n = r_tot + cr, w_tot + cw, s_tot + ls, n + 1
                res.edit(rk, row)
                whole.edit(rk, row)
                ref, _ = SY.scratch(h, res.table, res.keys)
                ok &= all(res.verdict(k) == ref[k] for k in res.keys)
        ckpt_entries = sum(len(st[0]) + 1 for ck, _rd in res.trace.values() for _k, st in ck)
        check(ok and same_set and r_tot <= w_tot,
              "s2 seed %d resume: %d edits and reverts agree with the decoder run whole, same queries "
              "re-derived as before; lookups %d resumed vs %d whole-query vs %d from scratch "
              "(checkpoints held: %d heap entries)" % (seed, n, r_tot, w_tot, s_tot, ckpt_entries))
        COUNTS["s2 seed %d resume" % seed] = {"edits": n, "lookups_resumed": r_tot,
                                             "lookups_whole_query": w_tot, "lookups_scratch": s_tot,
                                             "checkpoint_heap_entries": ckpt_entries}
        rng = random.Random(seed + 19)
        chain_ok = True
        for _ in range(60):
            rk = rng.choice(sorted(dict.keys(res.table), key=repr))
            row = dict.get(res.table, rk)
            res.edit(rk, SY.overlay(row, rng.choice(row)[0], rng.choice([Fraction(2), Fraction(1, 2), Fraction(3)])))
            ref, _ = SY.scratch(h, res.table, res.keys)
            chain_ok &= all(res.verdict(k) == ref[k] for k in res.keys)
        check(chain_ok, "s2 seed %d resume: 60 chained edits, checkpoints carried across edits, agree after every edit"
              % seed)
    # mutant: resume one read too late (skips re-reading the edited key)
    table = h.build_table(11)
    queries = h.queries_for(table, 11)
    caught = False
    for rk0 in sorted({k for k in table}, key=repr)[:12]:
        mut = SY.ResumeEngine(h, table, queries)
        mut.build()
        orig = mut._derive
        def late(qk, start_at=None, _o=orig, _m=mut):
            if start_at is not None and start_at + 1 < len(_m.trace[qk][0]):
                start_at += 1
            return _o(qk, start_at)
        mut._derive = late
        row = dict.get(mut.table, rk0)
        try:
            mut.edit(rk0, SY.overlay(row, row[0][0], Fraction(3)))
        except AssertionError:
            caught = True  # the carried-read hash recheck refuses the late resume
            continue
        ref, _ = SY.scratch(h, mut.table, mut.keys)
        caught |= any(mut.verdict(k) != ref[k] for k in mut.keys)
    check(caught, "s2 mutant (resume one checkpoint past the first read of the edited key) is caught "
                  "(by the carried-read hash recheck)")
    # mutant: missing-row lookups dropped from the cone
    table = h.build_table(11)
    queries = h.queries_for(table, 11)
    mut = SY.Engine(h, table, queries, drop_missing_mutant=True)
    mut.build()
    caught = False
    real = SY.Engine(h, table, queries)
    real.build()
    for k in real.keys:
        for rk, hh in real.state[k][1].items():
            if hh == SY.MISSING and not caught:
                mut.edit(rk, [(0, Fraction(1))])
                ref, _ = SY.scratch(h, mut.table, mut.keys)
                caught |= any(mut.verdict(q) != ref[q] for q in mut.keys)
                mut.edit(rk, None)
    check(caught, "s2 mutant (missing-row lookups not taken as premises) is caught by the checker")


# ---------------------------------------------------------------- system 3

def synth_table(model, name, n_axes, dom, n_rows, seed):
    rng = random.Random(seed)
    axes = [{"name": chr(97 + i), "values": list(range(dom))} for i in range(n_axes)]
    comps = ["p%d" % i for i in range(6)]
    seen, rows = set(), []
    while len(rows) < n_rows:
        cfg = tuple(rng.randrange(dom) for _ in range(n_axes))
        if cfg in seen:
            continue
        seen.add(cfg)
        rows.append(cfg)
    def beh(cfg):
        # each component reads a fixed small set of axes
        return {"p0": cfg[0] % 2, "p1": (cfg[0] + cfg[1]) % 2, "p2": cfg[2] * cfg[3] % 3,
                "p3": cfg[4] % 2, "p4": (cfg[1] + cfg[5]) % 2 if n_axes > 5 else 0,
                "p5": int(cfg[0] == cfg[n_axes - 1])}
    edges = [{"components": ["p0", "p1"], "weight": 2}, {"components": ["p2", "p3"], "weight": 3},
             {"components": ["p1", "p4", "p5"], "weight": 1}, {"components": ["p3"], "weight": 1}]
    doc = {"format": "hma-table-v1", "name": name, "axes": axes, "components": comps,
           "contract": [{"configuration": {chr(97 + i): c[i] for i in range(n_axes)},
                         "behavior": beh(c)} for c in rows],
           "edges": edges}
    return doc


def load_doc(model, doc, path):
    with open(path, "w") as f:
        json.dump(doc, f)
    return model.load_table(path)


def s3(solver_dir, tmp):
    home(solver_dir)
    need("AX")
    model, solver = AX.load_solver(solver_dir)
    fx = os.path.join(solver_dir, "fixtures")
    for f in sorted(os.listdir(fx)):
        t = model.load_table(os.path.join(fx, f))
        e = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, (), t.edges))
        ok = e.result() == solver.solve(e.table())
        for r in t.contract:
            e.join([r])
            ok &= e.result() == solver.solve(e.table())
        check(ok, "s3 %s: incremental result equals solver.py's from scratch at every one of %d row-append "
                  "prefixes (full JSON result)" % (f, len(t.contract) + 1))
    # 6-axis synthetic, 200 -> 220 rows
    for dom, label in ((3, "dense"), (2, "binary")):
        n_rows = 220 if dom == 3 else 60
        base = n_rows - 20
        doc = synth_table(model, "synthetic-%s" % label, 6, dom, n_rows, 41)
        full_t = load_doc(model, doc, os.path.join(tmp, "s3-%s.json" % label))
        e = AX.AxisEngine(model, model.Table(full_t.name, full_t.axes, full_t.components,
                                             full_t.contract[:base], full_t.edges))
        built = e.pairs_computed
        t0 = time.perf_counter()
        pairs, rem = e.join(full_t.contract[base:])
        t_inc = time.perf_counter() - t0
        t0 = time.perf_counter()
        ref = solver.solve(full_t)
        t_scr = time.perf_counter() - t0
        exp_pairs = n_rows * (n_rows - 1) // 2 - base * (base - 1) // 2
        check(e.result() == ref and pairs == exp_pairs,
              "s3 synthetic-%s 6 axes, %d -> %d rows: join computed %d new pairs vs %d from scratch, "
              "re-measured %d of 64 subsets; agrees with solver.py (wall %.1f ms vs %.1f ms, single run, "
              "indicative)" % (label, base, n_rows, pairs, ref["counts"]["contract_row_pairs"], rem,
                               t_inc * 1e3, t_scr * 1e3))
        COUNTS["s3 synthetic-%s" % label] = {"rows": [base, n_rows], "join_pairs": pairs,
                                             "scratch_pairs": ref["counts"]["contract_row_pairs"],
                                             "remeasured": rem, "subsets": 64,
                                             "wall_ms_indicative": [round(t_inc * 1e3, 1), round(t_scr * 1e3, 1)]}
    # staged join that opens a new axis: rows first hold axis f at 0, then vary it
    doc = synth_table(model, "staged", 6, 3, 400, 43)
    rows = doc["contract"]
    first = [r for r in rows if r["configuration"]["f"] == 0][:120]
    later = [r for r in rows if r["configuration"]["f"] != 0][:20]
    doc["contract"] = first + later
    t = load_doc(model, doc, os.path.join(tmp, "s3-staged.json"))
    e = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, t.contract[:120], t.edges))
    pairs, rem = e.join(t.contract[120:])
    f_bit = 1 << 5
    only_f = all(S & f_bit for S in e.remeasured)
    check(e.result() == solver.solve(t) and 0 < rem < 32 and only_f,
          "s3 staged: 20 rows that first vary axis f re-measure %d subsets, all containing f (at most 32 can); "
          "agrees with solver.py" % rem)
    COUNTS["s3 staged"] = {"remeasured": rem, "subsets_containing_f": 32, "pairs": pairs}
    # 2-axis scoping, strictly below the maximum
    base_doc = {"format": "hma-table-v1", "name": "two-axis", "components": ["p", "q"],
                "axes": [{"name": "a", "values": [0, 1]}, {"name": "b", "values": [0, 1]}],
                "edges": [{"components": ["p", "q"], "weight": 1}],
                "contract": [
                    {"configuration": {"a": 0, "b": 0}, "behavior": {"p": 0, "q": 0}},
                    {"configuration": {"a": 1, "b": 0}, "behavior": {"p": 1, "q": 0}}]}
    join_rows = [{"configuration": {"a": 1, "b": 1}, "behavior": {"p": 1, "q": 1}}]
    t0d = load_doc(model, base_doc, os.path.join(tmp, "s3-2a.json"))
    full = dict(base_doc, contract=base_doc["contract"] + join_rows)
    t1 = load_doc(model, full, os.path.join(tmp, "s3-2b.json"))
    e = AX.AxisEngine(model, t0d)
    _p, rem = e.join(t1.contract[2:])
    check(e.result() == solver.solve(t1) and rem == 2,
          "s3 two-axis: a join re-measures %d of 4 subsets ({b} and {a,b}; the empty subset can never be live, "
          "so 3 of 4 is the maximum, not evidence of scoping); agrees with solver.py" % rem)
    # deletions: support counts keep alternate supports; cone-scoped re-measure
    for f in sorted(os.listdir(fx)):
        t = model.load_table(os.path.join(fx, f))
        e = AX.AxisEngine(model, t)
        ok = True
        for r in list(t.contract)[::-1]:
            e.withdraw([r.configuration])
            ok &= e.result() == solver.solve(e.table())
        check(ok, "s3 %s: withdrawing rows one by one back to empty agrees with solver.py after every step" % f)
    t = model.load_table(os.path.join(tmp, "s3-staged.json"))
    e = AX.AxisEngine(model, t)
    released, rem = e.withdraw([r.configuration for r in t.contract[120:]])
    e120 = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, t.contract[:120], t.edges))
    only_f = all(S & (1 << 5) for S in e.remeasured)
    check(e.result() == solver.solve(e.table()) and e.live == e120.live and 0 < rem and only_f,
          "s3 staged: withdrawing the 20 f-varying rows releases %d pairs, re-measures %d subsets (all containing f) "
          "and returns exactly the 120-row state; agrees with solver.py" % (released, rem))
    COUNTS["s3 staged withdrawal"] = {"pairs_released": released, "remeasured": rem}
    t = model.load_table(os.path.join(tmp, "s3-dense.json"))
    e = AX.AxisEngine(model, t)
    rng = random.Random(17)
    cfgs = [r.configuration for r in t.contract]
    ok, rems, steps = True, [], 0
    while cfgs:
        pick = rng.sample(cfgs, min(len(cfgs), rng.randint(1, 12)))
        for c in pick:
            cfgs.remove(c)
        _p, r = e.withdraw(pick)
        rems.append(r)
        steps += 1
        ok &= e.result() == solver.solve(e.table())
    check(ok, "s3 synthetic-dense: %d random withdrawals from 220 rows to empty agree after every step; "
              "subsets re-measured per step: %d zero, max %d, total %d (full rebuild would re-measure 64 each)"
              % (steps, rems.count(0), max(rems), sum(rems)))
    COUNTS["s3 dense withdrawal chain"] = {"steps": steps, "zero_steps": rems.count(0), "max": max(rems),
                                           "total_remeasured": sum(rems)}
    # changed behavior cell = withdrawal plus join, named
    t = model.load_table(os.path.join(tmp, "s3-staged.json"))
    e = AX.AxisEngine(model, t)
    row = t.contract[0]
    beh = dict(row.behavior)
    beh["p3"] = 1 - beh["p3"] if beh["p3"] in (0, 1) else 0
    newrow = model.Row(dict(row.configuration), beh)
    e.withdraw([row.configuration])
    e.join([newrow])
    doc2 = json.load(open(os.path.join(tmp, "s3-staged.json")))
    doc2["contract"] = doc2["contract"][1:] + [{"configuration": newrow.configuration, "behavior": beh}]
    check(e.result() == solver.solve(load_doc(model, doc2, os.path.join(tmp, "s3-changed.json"))),
          "s3: a changed behavior cell handled as withdrawal plus join agrees with solver.py")
    # mutant: overdelete without rederive (alternate supports ignored)
    t = model.load_table(os.path.join(tmp, "s3-dense.json"))
    m = AX.AxisEngine(model, t)
    m.withdraw([r.configuration for r in t.contract[:5]], count_mutant=True)
    check(m.result() != solver.solve(m.table()),
          "s3 mutant (a component dropped at its first lost support, alternate supports ignored) is caught")
    # refusal: changed behavior at an existing configuration is not a join
    bad = model.Row({"a": 1, "b": 1}, {"p": 0, "q": 0})
    e = AX.AxisEngine(model, t1)
    try:
        e.join([bad])
        refused = False
    except AX.NotAJoin:
        refused = True
    check(refused, "s3: join refuses a changed behavior cell at an existing configuration (it must come as withdrawal plus join)")
    # a refused batch changes nothing: a valid new row followed by a duplicate, and a
    # batch that repeats its own new row, are refused before any carried state moves
    atomic = True
    for label in ("x", "d"):
        t = model.load_table(os.path.join(solver_dir, "fixtures", label + ".json"))
        k = len(t.contract) // 2
        e = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, t.contract[:k], t.edges))
        snap = (list(e.rows), dict(e.dc), dict(e.cnt), dict(e.live), dict(e.measure), e.pairs_computed)
        for batch in ([t.contract[k], t.contract[0]], [t.contract[k], t.contract[k]]):
            try:
                e.join(batch)
                atomic = False
            except AX.NotAJoin:
                pass
            atomic &= (list(e.rows), dict(e.dc), dict(e.cnt), dict(e.live), dict(e.measure),
                       e.pairs_computed) == snap
        try:
            e.join(t.contract[k:])
            atomic &= e.result() == solver.solve(t)
        except AX.NotAJoin:
            atomic = False  # a half-applied refused batch left a row behind
    check(atomic, "s3: a refused join batch (a new row then a duplicate; a new row twice) leaves every carried "
                  "table unchanged, and the engine then joins the rest and agrees with solver.py (x, d)")
    # mutant: re-measure only the subset equal to the mask
    caught = False
    for label in ("dense", "binary"):
        t = model.load_table(os.path.join(tmp, "s3-%s.json" % label))
        base = len(t.contract) - 20
        m = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, t.contract[:base], t.edges),
                          superset_mutant=True)
        m.join(t.contract[base:])
        caught |= m.result() != solver.solve(t)
    t = model.load_table(os.path.join(tmp, "s3-staged.json"))
    m = AX.AxisEngine(model, model.Table(t.name, t.axes, t.components, t.contract[:120], t.edges),
                      superset_mutant=True)
    m.join(t.contract[120:])
    caught |= m.result() != solver.solve(t)
    check(caught, "s3 mutant (supersets of a grown difference set not re-measured) is caught by the checker")


FIXTURE = os.path.join(HERE, "fixtures", "semantic-axes-points.json")


def points():
    """The s1 fixture ships with the candidate-space home only
    (software-redundant-compute-expands, examples/incremental-recomputation/fixtures).
    Elsewhere s1 needs its path; refuse by name rather than skip."""
    if not os.path.exists(FIXTURE):
        sys.exit("s1 needs the semantic-axes points fixture, which is not in this checkout: "
                 "pass its path (gate.py s1 <points.json>), or run 'all' from "
                 "software-redundant-compute-expands examples/incremental-recomputation")
    return FIXTURE


def main():
    args = sys.argv[1:]
    if not args:
        print(__doc__)
        return 2
    mode = args[0]
    tmp = os.path.join(HERE, ".gate-tmp")
    os.makedirs(tmp, exist_ok=True)
    out = None
    if mode == "all":
        rev, prlm, hma = args[1:4]
        out = args[4] if len(args) > 4 else None
        s1(points())
        s1_meta(os.path.join(rev, "meta.py"))
        s2(os.path.join(prlm, "harness", "run.py"))
        s3(os.path.join(hma, "solver"), tmp)
    elif mode == "s1":
        s1(args[1] if len(args) > 1 else points())
    elif mode == "meta":
        s1_meta(args[1] if len(args) > 1 else os.path.join(HERE, "..", "meta.py"))
    elif mode == "s2":
        s2(args[1] if len(args) > 1 else os.path.join(HERE, "..", "run.py"))
    elif mode == "s3":
        s3(args[1] if len(args) > 1 else os.path.join(HERE, ".."), tmp)
    else:
        print(__doc__)
        return 2
    import shutil
    shutil.rmtree(tmp, ignore_errors=True)
    ok = all(RESULTS) and bool(RESULTS)
    print("GATE: %s (%d checks, %d failed)" % ("PASS" if ok else "FAIL", len(RESULTS),
                                               RESULTS.count(False)))
    if out:
        with open(out, "w") as f:
            json.dump(COUNTS, f, indent=1, sort_keys=True, default=str)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
