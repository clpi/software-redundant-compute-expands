# Incremental recomputation: the candidate-space frontier (system 1)

The candidate space's frontier as a carried dominance matrix: a join costs
2(n-1) ordered evaluations, a re-join with unchanged scores costs 0, a
withdrawal costs 0 and re-admits exactly what the withdrawn item blocked, and
a score change is a withdrawal plus a join. The from-scratch frontier stays,
as the checker only (`naive_frontier`).

- `frontier.py`: engine and checker.
- `gate.py s1`: engine vs checker at every append prefix on the semantic axes
  candidate vectors (fixtures/, exported from that lane's log with its sha256),
  join order, carry, withdrawal, score change, premise hashes, and a mutant
  that must be caught.
- `lean/`: `Cone.front_join`, `Cone.front_withdraw` and the generic lookup and
  pair cone rules; `LEAN=... sh lean/check.sh`.
- SPEC.md and RESULTS.md cover all three systems; the other two engines land
  in their own homes (the PRLM repo and the HMA repo), the meta-search in the
  reversible repo. `receipts/` holds the full cross-home gate run.

Run: `python3 -B gate.py s1` and `LEAN=/path/to/lean-4.19.0 sh lean/check.sh`.
