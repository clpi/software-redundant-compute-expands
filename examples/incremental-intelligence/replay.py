import json
from itertools import permutations
from math import prod

from receipts import Event, Replica, lane


def require(ok, reason):
    if not ok:
        raise ValueError(reason)


def run():
    a, m = lane("design", ["start", "scope", "clarify the joint constraint"])
    b, n = lane("execution", ["ready", "reported"])
    pieces = [Replica(frozenset([a[0], b[1]]), frozenset([m[2], n[1]])),
              Replica(frozenset([a[2], b[0]]), frozenset([m[0]])),
              Replica(frozenset([a[1]]), frozenset([m[1], n[0]]))]
    base = pieces[0]
    require(base.receipt("design",2)==("missing",(1,2)),"drop undetected")
    require(base.receipt("execution",1)==("missing",(0,)),"dependency drop undetected")
    expected = pieces[0].join(pieces[1]).join(pieces[2])
    for i,j,k in permutations(range(3)):
        require(pieces[i].join(pieces[j].join(pieces[k])).join(pieces[i])==expected,
                "join order or duplicate altered receipt")
        require(expected.receipt("design",2)==("complete-through",2),"delivery did not recover")
        require(expected.receipt("execution",1)==("complete-through",1),"bad execution horizon")
    require(expected.receipt("design",3)==("stale",2),"old boundary presented as current")
    require(expected.receipt("unobserved",0)==("unsupported",-1),"unseen source treated complete")
    alt = Event("design",1,a[0].digest,"contradiction")
    conflict = expected.join(Replica(frozenset([alt])))
    require(conflict.receipt("design",2)==("conflict",2),"silent overwrite")
    # Controlled consequence: a typed fact qualifies all previously blocked
    # product families. Explicitly enumerate to check the represented count.
    axes = [[f"{i}:{j}" for j in range(3)] for i in range(8)]
    def unfold(families):
        plans = [()]
        for family in families:
            plans = [r+(i,) for r in plans for i in family]
        return plans
    def qualifies(replica):
        # Controlled decoder, not a claim of general natural-language parsing.
        return replica.receipt("design",2)==("complete-through",2) and any(
            e.source=="design" and e.sequence==2
            and e.payload=="clarify the joint constraint" for e in replica.events)
    expanded = unfold(axes) if qualifies(expected) else []
    wrong_events, wrong_marks = lane("design", ["start", "scope", "unrelated"])
    wrong = Replica(frozenset(wrong_events), frozenset(wrong_marks))
    require(wrong.receipt("design",2)==("complete-through",2) and not qualifies(wrong),
            "delivery completeness confused with semantic evidence")
    require(len(set(expanded))==prod(map(len,axes))==6561 and not qualifies(base),
            "incorrect support count")
    return {"schema":"incremental-intelligence.synthetic-convergence.v1",
            "replica_orders":6, "duplicate_idempotence":True,
            "drop_before_reconciliation":True,"out_of_order_reconciliation":True,
            "stale_refused":True,"unrelated_complete_input_refused":True,"unobserved_unsupported":True,"conflict_visible":True,
            "typed_clarifications":1,"independent_choice_families":len(axes),
            "qualified_synthetic_combinations_after":len(expanded),
            "network_transport_tested":False,"signatures_tested":False}


if __name__=="__main__":
    print(json.dumps(run(), indent=2, sort_keys=True))
