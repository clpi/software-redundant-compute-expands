# Scoped automated abduction

Start from a finite, qualified projection of the append-only Idol hypergraph.
A support is a subset of declared **hypothetical** actions that derives every
goal and no forbidden atom. These hypotheses do not become observations,
execution grants, or constructors of canonical progress.

- `abduction.py INPUT.json`: uses the existing action-support worklist and
  antichain closure. Complete premise lists are used for firing. Backward
  reachability only identifies the relevant slice. Identical appends are
  idempotent and conflicting identities are refused before mutation. New
  rules and facts wake existing supports; a newly witnessed blocker can
  revoke current use of a previously returned hypothetical explanation.
- `check_abduction.py INPUT.json CERT.json`: independent witness checker.
  Checks exact scoped source bytes for the slice, proof steps, unsupported
  assumptions, every single omission for minimality, and a finite partition
  proving no solution is omitted. It independently computes dominance and
  the weighted selection. No search results authorize an effect or prove
  that the caller's raw observations are faithful.
- `native_fixture.py` specializes the same finite input to an Idol subset
  oracle (up to 62 symbols and 20 assumptions, explicit refusal beyond).
  The emitted solver itself is Idol; JSON handling/projection and production
  certificate checking here are Python. A bounded, unrolled saturation
  path is used. The loop-carried alternative produced a wrong support on
  the historical native and direct backends and is not offered.
- `idol_case.py`: uses the old merged #12 ledger to derive the actual
  eight-capability continuation gap from two executions. It discovers two
  incomparable hypothetical explanations. Its two resource axes are
  illustrative costs, not measured resource use. If the old ledger is
  repaired, the historical example must run against its original pin. The
  repaired default reports the exact warm/cold agreement and no hypothetical
  action. Use `--expect repaired` to require that outcome, or `--expect historical`
  to require the original discrepancy.

```sh
python3 abduction.py example.json > example.cert.json
python3 check_abduction.py example.json example.cert.json
python3 verify.py
python3 test_native.py /absolute/path/to/idol
python3 idol_case.py --expect repaired
python3 idol_case.py --expect historical --example-dir /path/to/merged-12/examples/monotone-synthesis
```

The proof imports the actual `Canon` definitions. It validates assumption
monotonicity, the authority separation, completeness of a checked interval
cover, exactness of premise-closed slicing, and the single-omission bound.
The external checker implements the cover semantics; no Lean-to-Python
refinement proof is claimed. Ranking is separate from support membership;
nonnegative additive costs are the only optimization model in this example.
Worst-case search and output can both be exponential. There is no
unbounded/timeout completeness claim. New graph evidence is retained, but
a certificate is usable only for the exact query projection it binds.

### Weight-only replay

`Ledger.prepare(query)` returns a historical immutable snapshot. Call
`snapshot.reweight(weights)` for a small policy update instead of resending
the supports and cover. The independent checker exposes a process-local
verifier when called with `replay(..., _return_policy=True)` after it has
checked the full certificate. Neither handle is a release receipt, a network
protocol, or a statement that this projection remains current after an append.

The grouping is exact: equal cost vectors mutually fail strict dominance;
a vector's dominance status applies to every support in that group. The
checker independently visits unique vectors in lexicographic order. A
strict componentwise dominator must be earlier; if discarded, it has an
earlier surviving dominator by transitivity. Policy selection uses only the
lexicographically first support of each surviving vector because all
supports at that vector receive the same weighted score. The complete
frontier still retains all tied supports, including undominated vectors
unsupported by a positive linear weighting.

A relevant graph, cost or axis change requires a new binding and a new cold
checker pass. An append clears the fast current-query index; exact projection
identity may still reuse state once re-established. The current-index check
serializes the query identity, but touches no graph on a weight-only request.
Old verified policy handles explicitly certify only the old digest.
`verify_reweight.py` tests 4,096 policies and attacks this boundary.
`benchmark_reweight.py --baseline <previous-abduction.py>` reports raw
paired warm timings. The old API materializes a full certificate because
it has no policy-only route; the new API checks a policy delta instead.
This is a scoped Python replay, not an Idol-native performance claim.
