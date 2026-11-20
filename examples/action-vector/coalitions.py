"""Check compositional growth and reweighting without executing any UI action."""
import json
from itertools import product
from action_support import Edge, Supports, choose, frontier, key


def run():
    s = Supports()
    stages = []
    for n in range(1, 9):
        goal = f"goal-{n}"
        s.append(witnesses=[(goal, f"{n}-{route}") for route in ("a","b","c")])
        roots = tuple(f"goal-{i}" for i in range(1,n+1))
        prior = s.evaluations
        reach = s.require_all(roots)
        if len(reach) != 3**n or any(len(x) != n for x in reach):
            raise ValueError("coalition count disagrees with independent product formula")
        expected = {frozenset(f"{i}-{r}" for i,r in enumerate(y,1))
                    for y in product(("a","b","c"), repeat=n)}
        if set(reach) != expected:
            raise ValueError("coalition membership disagrees with independent oracle")
        stages.append({"requirements":n, "witness_actions":3*n, "minimal_plans":len(reach),
                       "support_rule_evaluations_for_projection":s.evaluations-prior})
    # Compress 6,561 explicit plan rows into a product of eight local pools.
    # A new witness covers all outputs; keep independent fallbacks.
    goals = tuple(f"goal-{i}" for i in range(1,9))
    s.append(witnesses=[(goal,"shared") for goal in goals])
    joined = s.require_all(goals)
    if len(joined) != 6562 or joined[0] == ():
        raise ValueError("shared witness did not produce exactly one alternate")
    allowed = [(frozenset(["a"]),(0,4)),
               (frozenset(["b"]),(3,3)),
               (frozenset(["c"]),(4,0))]
    byplan = dict(allowed)
    pareto = frontier(byplan, byplan.__getitem__)
    if len(pareto)!=3:
        raise ValueError("weighted policy incorrectly removed an undominated plan")
    winners = sorted({key(choose(pareto,(i,j))[0]) for i,j in product(range(1,33),repeat=2)})
    # For every strictly positive weight, action b's cost is greater than
    # half the sum of the endpoint scores. The sample is a control, not the proof.
    if ("b",) in winners or any(2*(3*i+3*j) <= 4*i+4*j
                               for i,j in product(range(1,33),repeat=2)):
        raise ValueError("unreachable weighted point control")
    # A genuinely disjoint append never invokes a rule in the goal cone.
    s.append([Edge(("isolated","witness"),"elsewhere")],
             [("isolated","side-a"),("witness","side-b")])
    before = s.evaluations
    s.append(witnesses=[("isolated","side-c")])
    if s.require_all(goals) != joined or s.evaluations-before != 1:
        raise ValueError("disjoint scope leak")
    return {"schema":"candidate-space.coalitions.v1", "controlled_synthetic":True,
            "stages":stages, "shared_witness_minimal_plans":len(joined),
            "family_slots_before_shared_witness":24,
            "disjoint_append_rule_evaluations":s.evaluations-before,
            "unsupported_weighted_point":{"pareto_size":3, "weight_pairs_checked":1024,
                                          "weighted_winners":[list(x) for x in winners]}}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
