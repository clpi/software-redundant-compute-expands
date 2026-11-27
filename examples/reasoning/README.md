# Incremental Horn reasoning, measured against Vampire, E, Z3 and cvc5

`horn.py` and its native build `native/horn.c` decide function-free Horn clause sets without
equality (TPTP class CNF EPR HRN) by semi-naive forward chaining over one append-only clause
log: each new fact is joined only through the rule positions it can fill, so a clause appended
later costs only the derivations it enables. Argument indexes are built only for positions a
join looks up. A refutation is printed as its derivation DAG (`--proof-json`) and re-checked by
`check.py`, which has its own matcher.

`bench/bench.py` runs every solver as its own process on the same problem with the same wall
limit and keeps each solver's full output under its sha256. Peak memory comes from `wait4` in a
tiny fork shim (`bench/memrun.c`), because a forked child inherits its parent's peak resident
size across exec. `bench/table.py` summarizes; `bench/incr.py` is the incremental benchmark
(an answer after every appended clause).

## Engines

Forward chaining runs in doubling time slices beside two more engines (`native/core.c`), and
only forward chaining, which saturates, ever answers Satisfiable:

- ordered resolution with literal selection and subsumption (two argument orders): rule bodies
  resolve against rule heads, so rules compose into lemmas. The 2^30-step counter MSC015-1.030
  takes 466 resolutions; Vampire's proof search uses 4,524.
- equivalence search: a rule pair a->b, b->a whose rewrite fixes arguments to constants (an
  object loaded into a truck) rewrites every state to a normal form, and states grow forward from
  the facts while goals grow backward from the negated conjecture until one matches the other.
  Pairs that only permute arguments (cube moves) are not used as rewrites, which leaves plain
  bidirectional search. Once its shape check passes, equivalence search gets the same share of
  each slice as forward chaining: on a reachability problem a search from both ends needs far
  fewer states than one from the facts alone.

Resolution proofs are checked by `check_res.py`, which recomputes every binary resolvent and
compares up to renaming; equivalence-search proofs are replayed as ground steps and checked by
`check.py`. Both checkers reject tampered proofs. Batch mode no longer joins a rule against facts
while the file is read: queued facts meet every rule when they come off the queue.

## Horn clauses with function symbols and equality (`native/hyper.c`)

`horn` hands a problem with function symbols over variables, or with equality, to `hyper`, a term
engine built next to it. Terms are hash-consed; unification is structure sharing over banks with
an occurs check; discrimination trees index candidates for subsumption, resolution and rewriting.
Three engines run under one strategy schedule, each attempt in a fresh forked process:

- unit hyperresolution in a DISCOUNT given-clause loop (every derived clause is a positive unit),
  complete for Horn clauses;
- the same loop on a magic-set rewrite of the problem, which runs as tabled top-down resolution
  (only what the goal can use is derived);
- ordered resolution with a Knuth-Bendix order and literal selection, so rules compose into
  lemmas, plus superposition, equality resolution and forward and backward demodulation when the
  problem has equality.

The schedule is a list of (setting, seconds) chosen greedily by `bench/make_schedule.py` from
per-setting sweeps on one half of the problems (every other problem of the sorted list); results
are reported on the other half too, because a schedule fits the problems it was chosen on. After
the list, every setting runs again with doubling slices until the time limit.

`check_hyp.py` checks every refutation independently, with its own TPTP reader and unification:
hyperresolution steps (a derived unit must be an instance of the rule head under the unifier of
the body with the parents), binary resolution, superposition (rewrite at a stated position) and
equality resolution steps (each must be a variant of the recomputed conclusion). Magic-set
proofs are printed without the magic steps, which is why instances are accepted. Tampered proofs
are rejected.

Measured (receipts in `reasoning/receipts-terms`): the 562 TPTP v9.0.0 problems of class
CNF_UNS_RFO_NEQ_HRN, 30 s, two runs in parallel, same contract as above. All 562: native 510,
Vampire 509, E 519. Held-out half (not used to fit the schedule): native 253, Vampire 255, E 257.
Every native proof checks. Native solves 3 that neither baseline solves. On the 490 all three
solve, median wall is 18.6 ms native, 21.3 ms Vampire, 12.9 ms E, and median peak memory 2.1 MB,
9.2 MB, 5.7 MB. Open: E solves 20 problems native does not, mostly condensed-detachment logic
calculi (LCL), and is faster by median. The equality class
(450 problems, CNF_UNS_RFO_SEQ_HRN) is still behind: native 309, Vampire 415, E 372 (held-out half:
151, 204, 183), every native proof checked, up from 270 after definition unfolding, unit
simplification, ordered rewriting, equality subsumption and a refitted schedule
(`bench/sched-eq-v2.txt`). On the 303 all three solve, median wall is 14.7 ms native, 120.5 ms
Vampire, 20.4 ms E.

## Measured (receipts in the project files, `reasoning/receipts-hrn254-v4`)

254 TPTP v9.0.0 problems of class CNF_UNS_EPR_NEQ_HRN, 30 s wall limit, three runs in parallel
on 4 cores, all solvers in one run file. Vampire 5.1.2 (casc mode), E 3.5.12 (--auto), Z3 and
cvc5 1.4.2 (cvc5 with full-saturate-quant) on an SMT-LIB translation.

| solver | solved | median wall* | total wall* | median peak memory* | median proof steps* |
|---|---|---|---|---|---|
| native | 248 | 7.4 ms | 2.5 s | 2.8 MB | 6 |
| Vampire | 247 | 14.8 ms | 14.2 s | 9.3 MB | 6 |
| E | 242 | 23.3 ms | 16.4 s | 7.4 MB | 4 |
| Z3 | 235 | 34.6 ms | 22.1 s | 36.3 MB | - |
| cvc5 | 229 | 159.9 ms | 172.8 s | 48.7 MB | - |

\* on the 229 problems every solver solved. Every native refutation was checked. Native solves
everything any other solver solves, plus PLA031-1.008, which none of them solves in 30 s
(17.6 s, 49-step checked proof). Head to head with Vampire on the 247 both solve: native uses
less memory on all 247 and is faster on 231. Proof steps are counted differently per prover
(native: hyperresolution or resolution steps; E: its proof object lines), so that column is a
rough comparison only.

Losses, open: Vampire is faster on 16 problems, 15 of them by under 7 ms on runs of about 10 ms
(start-up noise) and SYN102-1.007.007 by 0.35 s (0.47 s against 0.12 s). E's proofs are shorter
by median. Nobody solves PUZ056-2.015 and up (Towers of Hanoi, 15 to 30 disks) in 30 s; that
needs tower-moving lemmas with side conditions, which neither new engine finds yet.

Fixed on the way: the first native run saturated after every clause, so on the Rubik's cube
problems (PUZ037-2/3) it explored the subgroup generated by the first four moves before the moves
that reach the goal arrived. The incremental harness also lost native's answers when it timed
out, because they were not flushed; each answer is now flushed.

After v4 (build with the equal share and a replay fix): native still solves the same 248, all
248 proofs check, total wall on them drops from 21.8 s to 10.5 s, and PLA031-1.008 drops from
17.1 s to 5.8 s. The replay fix: a rule whose head has a variable its body leaves free (rule1 of
PUZ056-2, the smallest disk moved to any peg) was replayed with that variable set to the first
constant, so the PUZ056-2.010 proof failed the checker; the replay now unifies the head with the
goal it was reached from, as the backward step did. Answer after every added clause, 30 problems,
5 s per answer, on the 19 that all five solvers finished (5,677 prefixes): native decides all
5,677 in 1.3 s total; Z3 decides 5,676 in 258 s, E 5,671 in 288 s, Vampire 5,674 in 666 s, cvc5
196 in 12,301 s; no decided answer disagrees with the majority, and native is faster and lighter
than every other solver on all 19 (PUZ037-2: 0.18 s, Z3 0.59 s).

Proofs: every native refutation in the v4 run checks. The 4,194,305-step forward proof of
MSC015-1.022 that ran the checker out of memory before is now a short resolution proof.
