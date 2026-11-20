"""Compiler-side index of the finite positive Canon.viewC closure."""
from collections import defaultdict, deque
from dataclasses import dataclass


@dataclass(frozen=True)
class Record:
    id: int
    level: int
    colors: tuple[int, ...]
    premises: tuple[int, ...]
    head: int


def projected(record, level, up, accept):
    if record.level > level or not accept(record.colors):
        return None
    def lift(value):
        for r in range(record.level, level):
            value = up(r, value)
        return value
    return tuple(map(lift, record.premises)), lift(record.head)


class Worklist:
    """Append-only under a fixed view. Callbacks must be immutable/pure.

    Full ordered edges are kept; only the readiness check deduplicates terms.
    Counter equals the number of distinct premises not yet processed.
    It is exact against derived membership at every quiescent prefix.
    """
    def __init__(self, level, up, accept):
        self._policy = (level, up, accept)
        self.records = []
        self.edges = set()
        self.derived = set()
        self.remaining = {}
        self.waiters = defaultdict(set)
        self.firing = {}
        self.new_edge_checks = self.waiter_visits = self.term_pops = 0

    def append(self, records):
        records = tuple(records)
        # Project the whole append before modifying state; a failed callback
        # should not publish part of an append.
        views = [projected(r, *self._policy) for r in records]
        self.records.extend(records)
        pending = deque()
        newly = []

        def fire(edge):
            head = edge[1]
            if head not in self.derived:
                self.derived.add(head)
                self.firing[head] = edge
                newly.append(head)
                pending.append(head)

        # Register against the same drained state for *all* new rules.
        # A zero rule's head must not be counted as already processed later
        # in this registration pass; seed the queue only after registration.
        ready = []
        for edge in views:
            if edge is None or edge in self.edges:
                continue
            self.edges.add(edge)
            self.new_edge_checks += 1
            premises = set(edge[0]) - self.derived
            self.remaining[edge] = len(premises)
            for p in premises:
                self.waiters[p].add(edge)
            if not premises:
                ready.append(edge)
        for edge in sorted(ready):
            fire(edge)
        while pending:
            p = pending.popleft()
            self.term_pops += 1
            for edge in sorted(self.waiters.pop(p, ())):
                self.waiter_visits += 1
                self.remaining[edge] -= 1
                if self.remaining[edge] == 0:
                    fire(edge)
        return tuple(newly)

    def audit_invariant(self):
        if self.term_pops != len(self.derived):
            raise ValueError("derived term processed more or less than once")
        for e in self.edges:
            missing = set(e[0]) - self.derived
            if self.remaining[e] != len(missing) or any(e not in self.waiters[p] for p in missing):
                raise ValueError("incorrect missing-premise index")
        for p, edges in self.waiters.items():
            if any(p in self.derived or p not in e[0] for e in edges):
                raise ValueError("unexpected waiter")
        return True
