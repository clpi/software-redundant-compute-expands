# Incremental, compounding intelligence

The design goal is **no manual relay and no silent drift across authorized
sources**. A single logical hypergraph survives separate processes, sessions,
or physical replicas. The observable result is the same scoped derivation
at the same delivered cut, not a requirement for one physical service and
not a claim that every service exposes its internal state.

## Contract

- Admit immutable events into one typed graph. An event binds a source lane,
  position, parent and content. Physical replicas reconcile by idempotent set
  union. Independent facts commute. Conflicting events at the same position
  remain visible and cannot become a single accepted answer by arrival order.
- A trusted source watermark binds a named prefix. A consumer must report
  **complete through that cut**, **missing**, **stale**, **conflict**, or
  **unsupported**. Reconcile missing ranges automatically wherever the owner
  has granted retrieval. Without a trustworthy watermark, an omitted tail is
  indistinguishable from one that doesn't exist. Never call a disconnected
  or inaccessible channel complete.
- Use typed source records and retain the highest fidelity acquired.
  Resolution is a projection parameter above the agreed coarsest view, not
  a lossy transport admission rule. Same delivered set, resolution, and color
  predicate must recompute the same logical projection. Authority, audience
  and snapshot remain part of every derived action contract.
- A compact clarification can qualify many downstream witnesses without
  becoming many independent records. Only declared rules, satisfied
  premises, and checked transforms produce evidence. Speculative synthesis
  may propose new facts but cannot authorize them or run effects.
- Fixed weight tensors, axis definitions, projected semantic/action vectors,
  and reweight patches belong to the same versioned graph, not an implicit
  cross-chat memory. Coefficient changes reuse evidence; axis or semantic
  changes invalidate dependent receipts. A transform is reversible at the
  scope where a left inverse is checked, or where the complementary residual
  is retained. A deterministic encoding is not proof of a unique intended
  meaning. Keep distinct weights and equivalent observable outcomes distinct.
- Idol is the native default harness, not a requirement for another tool to
  use the typed contract. No new transport or access grants are implied.

## Verified slice

The independent Lean module establishes ACI join, named-cut convergence,
missing-position detection, the unobservable-tail limit, and equivalence of
derived views and bounded closure under event-set identity. Run the full
`proof/check.sh`.

```sh
cd examples/incremental-intelligence
python3 -B replay.py | cmp - replay.json
```

The fixed synthetic run reconciles all six arrival permutations with
duplicates; detects dropped, stale, unknown and conflicting inputs; and
makes one typed clarification gate 6,561 enumerated combinations from eight
three-way families. This does not measure real channels or claim raw message
text is automatically translated into the right facts.

## Integration acceptance

For each authorized chat, bridge or worker, require a source sequence or
stable enumeration, a verifiable checkpoint and a bounded replay path.
Inject duplicate, reordered, unavailable, stale and conflicting data with
multiple readers. Measure actual end-to-end delay, throughput, catch-up
work and unsupported coverage separately, including the cost of finer
resolution. Require an authored fact to reach each destination audience
without cross-paste, with a missing-lane diagnostic under fault injection.
Reweight against immutable evidence, and verify any applied action and
inverse with independently observed state. Live connector wiring and the
native deterministic execution loop are not certified by these controls.
