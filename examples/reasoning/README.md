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

## Measured (receipts in the project files, `reasoning/receipts-hrn254`)

254 TPTP v9.0.0 problems of class CNF_UNS_EPR_NEQ_HRN, 30 s wall limit, 3 runs in parallel on
4 cores. Vampire 5.1.2 (casc mode), E 3.5.12 (--auto), Z3 and cvc5 1.4.2 (cvc5 with
full-saturate-quant) on an SMT-LIB translation.

| solver | solved | median wall* | total wall* | median peak memory* |
|---|---|---|---|---|
| native | 238 | 7.6 ms | 1.9 s | 2.9 MB |
| Vampire | 247 | 12.2 ms | 9.8 s | 9.3 MB |
| E | 242 | 20.4 ms | 7.3 s | 7.4 MB |
| Z3 | 236 | 33.8 ms | 19.6 s | 36.3 MB |
| cvc5 | 230 | 144.4 ms | 181.9 s | 48.8 MB |

\* on the 228 problems every solver solved. Head to head with Vampire on the 238 both solve:
native is faster on 227 and uses less memory on 235.

Losses, open: Vampire solves 9 that native does not (MSC015-1.022/025/027/030, PLA031-1.005/006/007,
PUZ037-2/3); E 6, Z3 and cvc5 2 each. They are counters, planning and puzzles whose ground state
space is exponential; Vampire solves them by resolving rules with rules into shortcuts (4,524
resolution steps for a 2^30-step counter). The engine grounds every step. A saturation core with
rule composition and subsumption is the open work order. MSC015-1.022 is solved by native alone
in 7.1 s (4,194,304 facts) and its 1 GB proof checks; in the parallel run the checker ran out of
memory, recorded as not checked.
