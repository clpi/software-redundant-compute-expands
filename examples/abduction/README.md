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
  repaired, the historical example must run against its original pin.

```sh
python3 abduction.py example.json > example.cert.json
python3 check_abduction.py example.json example.cert.json
python3 verify.py
python3 test_native.py /absolute/path/to/idol
python3 idol_case.py --example-dir /path/to/merged-12/examples/monotone-synthesis
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
