#!/usr/bin/env python3
"""System 1: incremental Pareto frontier with a carried dominance matrix.

Rule (SPEC.md, system 1): dominance between two items depends only on
those two items' score vectors (pair locality). A join of item y can
change only the ordered pairs (y, x) and (x, y). Carried state: the
score vector and its hash per item (the premise), and, per item, the
set of items that dominate it. The frontier is the set of items with
no dominator. Joins are append only; a changed score vector is a
withdrawal plus a join, named as such. A withdrawal costs zero
comparisons because the matrix is carried: removing y from every
dominator set re-admits exactly the items y alone was blocking.

The checker (naive_frontier) is written separately and shares no code
with the engine: it recomputes every ordered pair from scratch.

Counts are the claims. evals counts ordered dominance evaluations.
Stdlib only, deterministic.
"""
from __future__ import annotations

import hashlib
import json


def premise(vec):
    """Hash of an item's score vector: the premise its pairs rest on."""
    return hashlib.sha256(json.dumps(list(vec)).encode()).hexdigest()[:16]


class Frontier:
    """Carried dominance state over items with score vectors.

    sense: per axis, +1 if higher is better, -1 if lower is better.
    """

    def __init__(self, sense, one_direction_mutant=False):
        self.sense = tuple(sense)
        self.vec = {}
        self.hash = {}
        self.dominators = {}   # item -> set of items that dominate it
        self.dominates_of = {}  # item -> set of items it dominates
        self.evals = 0
        self.log = []          # (op, item, evals spent)
        self._mutant = one_direction_mutant

    def _dom(self, a, b):
        """a dominates b: no worse on every axis, better on one."""
        self.evals += 1
        va, vb = self.vec[a], self.vec[b]
        better = False
        for s, x, y in zip(self.sense, va, vb):
            if s * x < s * y:
                return False
            if s * x > s * y:
                better = True
        return better

    def join(self, item, vec):
        vec = tuple(vec)
        if len(vec) != len(self.sense):
            raise ValueError("axis count mismatch for %r" % (item,))
        h = premise(vec)
        if item in self.vec:
            if self.hash[item] == h:
                self.log.append(("carry", item, 0))
                return "carry"
            self.withdraw(item, reason="score change")
        before = self.evals
        self.vec[item] = vec
        self.hash[item] = h
        self.dominators[item] = set()
        self.dominates_of[item] = set()
        for other in list(self.vec):
            if other == item:
                continue
            if self._dom(item, other):
                self.dominators[other].add(item)
                self.dominates_of[item].add(other)
            if self._mutant:
                continue  # MUTANT: the reverse direction is never evaluated
            if self._dom(other, item):
                self.dominators[item].add(other)
                self.dominates_of[other].add(item)
        self.log.append(("join", item, self.evals - before))
        return "join"

    def withdraw(self, item, reason="withdrawal"):
        for other in self.dominates_of.pop(item):
            self.dominators[other].discard(item)
        for other in self.dominators.pop(item):
            self.dominates_of[other].discard(item)
        del self.vec[item], self.hash[item]
        self.log.append(("withdraw:" + reason, item, 0))

    def frontier(self):
        return sorted(i for i, d in self.dominators.items() if not d)

    def recheck_premises(self):
        """Every carried pair rests on hashes that still match the vectors."""
        return all(premise(v) == self.hash[i] for i, v in self.vec.items())


def naive_frontier(items, sense):
    """From-scratch checker: every ordered pair, no carried state.
    Returns (sorted frontier, ordered evaluations)."""
    evals = 0
    names = list(items)
    front = []
    for b in names:
        dominated = False
        for a in names:
            if a == b:
                continue
            evals += 1
            ge = all(s * x >= s * y for s, x, y in zip(sense, items[a], items[b]))
            gt = any(s * x > s * y for s, x, y in zip(sense, items[a], items[b]))
            if ge and gt:
                dominated = True
        if not dominated:
            front.append(b)
    return sorted(front), evals
