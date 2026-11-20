# Certified action vectors from the canonical graph

Use one append-only canonical record log. Syntax trees, screenshots, model
tensors, proposal text, measurements and effect receipts are separately typed
claims about it. Their hashes identify exact content, not equivalent meaning.
A projection is a named function of a graph revision, resolution, scope and
policy. Unrecognized data may be retained as bytes; absent a checked decoder
or semantic relation its action contribution is unknown. A lossy projection
can round-trip source bytes only with a residual or a proved inverse on its
declared quotient. Never infer a unique human intent or execution authority
from bytes, labels, or a score.

## One action epoch

1. Derive admissibility from the canonical graph using complete premises.
   Every element of the action vector records its operation, target, snapshot,
   preconditions, access/effect limits, expected observation, cost axes,
   and any checked inverse and associated output observation.
2. An explicit generator supplies checked action candidates. An obscurity
   vector can trigger an additional proposer when an axis crosses its own
   threshold. Explicit, proposed, and combined generators feed the **same**
   proof and authority gate. A proposal, high weight or low obscurity cannot
   pass that gate on its own.
3. Compute inclusion-minimal support antichains for joint goals, not a ranked
   list of isolated symbols. Across alternatives, take the union of plan
   families; across joint premises, take the union of their action sets over
   the product and remove strict supersets. Shared actions are paid once
   where effects permit that reuse. This is a derived view of the existing
   hypergraph. Retain factorized independent families rather than materialize
   their product until a query needs it.
4. Keep the actual nondominated objective vectors. Ranking a stable front
   uses a versioned vector of weights. Changing only ranking weights does not
   recompute support or delete the previously unselected Pareto points. A
   changed axis definition invalidates its metrics and frontier; a changed
   premise invalidates the dependent support slice. Selecting an already
   admitted candidate never certifies missing candidates or unseen outcomes.
   Exact dominance pruning assumes matched signatures and composable costs.
   A pruned strict superset is safe only for the stated nonnegative additive
   cost model, not for general plan-dependent cost or extra measured benefit.
5. Dispatch only with an explicit existing grant covering the exact target and
   bounded effects, after revalidating the pre-state. Append the independently
   observed result; an uncertain submit is not permission to replay. An
   inverse is authorized only against current scope and post-state. Executing
   it is not proved restoration until a fresh observable comparison passes.
6. Separate a goal threshold, dispatch refusal, and optimality stop. A goal
   threshold indicates an acceptable incumbent, not optimality. A certified
   stop requires the goal witness and coverage of all admissible alternatives:
   each can be refuted, already evaluated, or excluded by a checked bound.
   A tie requires an explicit deterministic tie certificate; absent a usable
   bound leave the contender unresolved. The stop predicate being independent
   of a scoring-only weight change applies to the eligibility-exhausted
   terminal case, not to a still-running weighted-bound search.

## Executable scope and verification

`action_support.py` is append-only positive Horn support with the Python tests
replaying every projection against exhaustive action subsets. Costs and
reversibility there are modeled contracts, not UI measurements. The planner
only enumerates its declared universe; the front is exact for those inputs,
not proof that another action cannot be constructed.

`action-experiment.py` is a separate synthetic bounded path oracle: fresh
dynamic programming and path enumeration verify the incremental front across
append, withdrawal and restore. It measures internal edge relaxations,
not wall-clock speed or the real native executor. `coalitions.py` checks
the factorization law and a Pareto point missed by scalar weighting.
The Lean file checks the abstract gate; these Python implementations have no
machine-checked refinement proof to it.

```sh
cd examples/action-vector
python3 -B -m unittest -q test_action_support
python3 -B coalitions.py | cmp - coalitions.json
python3 -B action-experiment.py | cmp - action-experiment.json
```

## Native integration gate

Use the existing Idol Eyes graph views, effect executor and inverse producer.
First run its exact pinned compiler and contract/runtime suites, without
skips. For each owned fixture: observe pre-state, check a graph grant, execute
one effect, independently observe output, construct a fresh inverse against
that output, execute and verify scoped restoration. Include wrong-session,
stale, ambiguous and partial outcomes; no automatic retries of uncertain
effects. Test the pure replay verifier without an executor. Only then compare
native action and stop sequences, qualification and elapsed costs against
matched baselines, including a state that can only be traversed with several
joint actions. No native execution or live browser result is claimed here.
