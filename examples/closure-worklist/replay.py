import json
from random import Random

from worklist import Record, Worklist


def oracle(records, level, up, accept):
    rules = set()
    for r in records:
        if r.level > level or not accept(r.colors):
            continue
        # Independent projection step: lift each entry of the ordered tuple
        # and the head together, then split. Repeated entries stay repeated.
        values = r.premises + (r.head,)
        for j in range(r.level, level):
            values = tuple(up(j, v) for v in values)
        rules.add((values[:-1], values[-1]))
    facts, work = set(), 0
    while True:
        heads = set()
        for ps, a in rules:
            work += 1
            if all(p in facts for p in ps):
                heads.add(a)
        grown = facts | heads
        if grown == facts:
            return facts, rules, work
        facts = grown


def tested_batches(batches, level, up, accept):
    old, prefixes, cold_work = [], 0, 0
    w = Worklist(level, up, accept)
    for batch in batches:
        old.extend(batch)
        previous = set(w.derived)
        delta = w.append(batch)
        expected, edges, work = oracle(old, level, up, accept)
        if w.derived != expected or w.edges != edges or set(delta) != expected - previous:
            raise ValueError("worklist differs from least closure")
        w.audit_invariant()
        cold_work += work
        prefixes += 1
    return dict(prefixes=prefixes, term_pops=w.term_pops, distinct_edges=len(w.edges),
                waiter_visits=w.waiter_visits, new_edge_checks=w.new_edge_checks,
                cold_rule_checks=cold_work)


def run():
    levels = (0, 1, 2)
    up = lambda level, term: term // 2
    accept = lambda colors: 1 in colors and 0 not in colors
    totals = {}
    for n in range(64):
        r = Random(n)
        batches = [
            [Record(5*i+j, r.randrange(4), r.choice([(1,), (0,), (0, 1), ()]),
                    tuple(r.randrange(18) for _ in range(r.randrange(4))), r.randrange(18))
             for j in range(5)] for i in range(10)
        ]
        for level in levels:
            a = tested_batches(batches, level, up, accept)
            for k,v in a.items():
                totals[k] = totals.get(k, 0) + v
    # Initially incomplete rules, projection aliases, a filtered duplicate,
    # zero premise activation, and an unsupported cycle.
    addressed = Worklist(1, up, accept)
    batches = [
        [Record(1,0,(1,),(4,5,5),8),Record(2,1,(0,1),(),2),
         Record(3,1,(1,),(10,),11),Record(4,1,(1,),(11,),10)],
        [Record(5,0,(1,),(),4),Record(6,1,(1,),(2,),6)],
        [Record(7,2,(1,),(),10)],
        [Record(8,1,(1,),(),10)],
    ]
    result = [list(addressed.append(b)) for b in batches]
    if result != [[],[2,6,4],[],[10,11]]:
        raise ValueError(f"targeted controls failed: {result}")
    # Replay against exact oracle after every update, not just at the end.
    tested_batches(batches,1,up,accept)
    # A chain first appears as 512 admitted rules. Only a later root unlocks
    # them; unrelated append then costs one admission without rescanning.
    chain = [[Record(i,0,(1,),(i-1,),i)] for i in range(1,513)]
    chain.extend([[Record(513,0,(1,),(),0)],[Record(514,0,(1,),(),900)]])
    large = tested_batches(chain,0,up,accept)
    return {"schema":"canonical-closure.worklist.v1",
            "comparison":"operation counts only; no wall-time or compiler integration claim",
            "random_projection_and_filter_controls":totals,"chain":large,
            "targeted_append_deltas":result}


if __name__ == "__main__":
    print(json.dumps(run(), sort_keys=True, indent=2))
