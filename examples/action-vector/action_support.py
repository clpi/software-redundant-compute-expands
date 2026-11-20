"""Inclusion-minimal witness plans on one append-only positive Horn hypergraph.

The action catalogue is an explicit finite universe; labels/proposals are not
premises or execution authority. The support index is a materialized projection.
"""
from collections import defaultdict, deque
from itertools import product
from typing import NamedTuple


class Edge(NamedTuple):
    premises: tuple[str, ...]
    head: str


def insert(old, support):
    if any(s <= support for s in old):
        return False
    old.difference_update({s for s in old if support < s})
    old.add(support)
    return True


def key(s):
    return tuple(sorted(s))


class Supports:
    def __init__(self):
        self.fact = defaultdict(set)
        self.edges = set()
        self.readers = defaultdict(set)
        self.evaluations = 0

    def append(self, edges=(), witnesses=()):
        changed, queue, pending = set(), deque(), set()

        def enqueue(edge):
            if edge not in pending:
                queue.append(edge)
                pending.add(edge)

        def wake(symbol, support):
            if insert(self.fact[symbol], support):
                changed.add(symbol)
                for edge in sorted(self.readers[symbol]):
                    enqueue(edge)

        for edge in sorted(set(edges) - self.edges):
            self.edges.add(edge)
            for token in set(edge.premises):
                self.readers[token].add(edge)
            enqueue(edge)
        for symbol, action in sorted(set(witnesses)):
            wake(symbol, frozenset((action,)))
        while queue:
            edge = queue.popleft()
            pending.remove(edge)
            self.evaluations += 1
            pools = [sorted(self.fact[a], key=key) for a in edge.premises]
            for tuple_of_supports in product(*pools):
                wake(edge.head, frozenset().union(*tuple_of_supports))
        return changed

    def require_all(self, symbols):
        # Factorized support families are stored per term. Products are
        # enumerated only for this explicit materialization request.
        candidates = {frozenset().union(*plan)
                      for plan in product(*(sorted(self.fact[a], key=key) for a in symbols))}
        by_size = defaultdict(list)
        for plan in sorted(candidates, key=lambda p: (len(p), key(p))):
            if not any(s < plan for size, pool in by_size.items() if size < len(plan) for s in pool):
                by_size[len(plan)].append(plan)
        return tuple(sorted((s for pool in by_size.values() for s in pool), key=key))


def frontier(plans, cost):
    """All objectives minimized. Nonnegative additive per-action axes."""
    plans = tuple(plans)
    vectors = {p: tuple(cost(p)) for p in plans}
    if (len(set(map(len, vectors.values()))) > 1
            or any(any(type(x) is not int or x < 0 for x in v) for v in vectors.values())):
        raise ValueError("invalid objective")
    return tuple(sorted(((p, a) for p, a in vectors.items()
                         if not any(all(x <= y for x, y in zip(b, a)) and b != a
                                    for b in vectors.values())), key=lambda x: key(x[0])))


def choose(pareto, weights):
    """Tie-break by stable action IDs; a weight change never rederives support."""
    if not pareto:
        return None
    if any(type(w) is not int or w < 0 for w in weights) or any(
            len(v) != len(weights) for _, v in pareto):
        raise ValueError("invalid weight vector")
    return min(pareto, key=lambda r: (sum(x*y for x,y in zip(weights,r[1])), key(r[0])))


def oracle(edges, witnesses, goals):
    """Independent exhaustive powerset oracle. Not used by the planner."""
    actions = sorted({a for _, a in witnesses})
    out = set()
    for mask in range(1 << len(actions)):
        selected = frozenset(a for i, a in enumerate(actions) if (mask >> i) & 1)
        facts = {s for s, a in witnesses if a in selected}
        while True:
            expanded = facts | {e.head for e in edges if all(p in facts for p in e.premises)}
            if expanded == facts:
                break
            facts = expanded
        if set(goals) <= facts:
            # Exhaustive subsets are enumerated before any strict superset.
            if not any(x < selected for x in out):
                out.add(selected)
    return out


def try_stop(goal_certified, winner_vector, open_bounds):
    """A lower-is-better box includes every unresolved contender.
    Strict improvement over a scalar threshold is not a stop certificate.
    Equal bounds refuse unless deterministic tie order is separately certified.
    """
    bounds = tuple(open_bounds)
    if not goal_certified or winner_vector is None:
        return False
    return all(len(v) == len(winner_vector) and
               all(a <= b for a,b in zip(winner_vector,v)) and
               any(a < b for a,b in zip(winner_vector,v)) for v in bounds)
