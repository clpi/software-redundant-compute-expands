"""Deterministic bounded reference for constructive release progress."""
from dataclasses import dataclass
from collections import defaultdict
from heapq import heappop, heappush
from itertools import product
from random import Random

# Authoritative finite fixture: dependencies are ordered. No unlabeled external
# read is permitted by this interpreter. Operators are pinned protocol data.
def run(op, xs):
    if op == "stable":
        return int(0 < xs[0] < 300)
    if op == "last":
        return xs[0][-1]
    if op == "effect":
        return xs[0] ^ (xs[1] & xs[2])
    if op == "same":
        return xs[0]
    if op == "pair":
        return xs
    raise ValueError(op)

@dataclass(frozen=True)
class Rule:
    name: str
    op: str
    parents: tuple

class Suite:
    def __init__(self, inputs, rules):
        self.inputs = tuple(inputs)
        self.rules = tuple(rules)
        self.position = {k:i for i,k in enumerate((*self.inputs, *(r.name for r in rules)))}
        if len(self.position) != len(self.inputs) + len(self.rules):
            raise ValueError("duplicate identity")
        self.readers = defaultdict(list)
        for i,r in enumerate(self.rules):
            for p in set(r.parents):
                if self.position[p] >= self.position[r.name]:
                    raise ValueError("cyclic or forward dependency")
                self.readers[p].append(i)

    def cold(self, x):
        if set(x) != set(self.inputs):
            raise ValueError("unspecified inputs")
        s = dict(x)
        for r in self.rules:
            s[r.name] = run(r.op, tuple(s[p] for p in r.parents))
        return s

    def recheck(self, old_inputs, old, x):
        # Caller supplies a verified full predecessor snapshot under this exact
        # suite. Ledger owns that snapshot; do not accept caller-provided caches.
        if x.keys() != old_inputs.keys():
            raise ValueError("changed input schema")
        o, waits, queued = dict(old), [], set()
        touched = []
        def wake(p):
            for i in self.readers[p]:
                if i not in queued:
                    heappush(waits, i)
                    queued.add(i)
        for p in self.inputs:
            if old_inputs[p] != x[p]:
                o[p] = x[p]
                wake(p)
        while waits:
            i = heappop(waits)
            r = self.rules[i]
            nxt = tuple(o[p] for p in r.parents)
            prev = tuple(old[p] for p in r.parents)
            if nxt == prev:
                continue
            touched.append(r.name)
            w = run(r.op, nxt)
            if w != old[r.name]:
                o[r.name] = w
                wake(r.name)
        return o, tuple(touched)

@dataclass(frozen=True)
class Proposal:
    name: str
    edit: tuple
    cost: tuple

@dataclass(frozen=True)
class Evaluation:
    predecessor: int
    proposal: Proposal
    inputs: tuple
    values: tuple
    recomputed: tuple

@dataclass(frozen=True)
class Progress:
    predecessor: int
    report_id: int

def improves(a,b):
    return len(a)==len(b) and all(0<=x<=y for x,y in zip(a,b))

class Ledger:
    def __init__(self, suite, inputs, cost, coordinates, possible):
        self.suite = suite
        self.coords = tuple(coordinates)
        self.possible = {k: frozenset(v) for k,v in possible.items()}
        self._edges = []
        self.inputs = dict(inputs)
        self.values = suite.cold(inputs)
        self.cost = cost
        self._edge(("origin", tuple(self.inputs.items()), tuple(self.values.items()), cost))
    @property
    def evidence(self):
        return tuple(self._edges)
    def _edge(self, row):
        self._edges.append(row)
        return len(self._edges)-1
    @property
    def current(self):
        return next(i for i in range(len(self._edges)-1,-1,-1)
                    if self._edges[i][0] in ("origin","progress"))
    def evaluate(self, p):
        if len({k for k,_ in p.edit})!=len(p.edit):
            raise ValueError("duplicate patch key")
        x = dict(self.inputs)
        x.update(p.edit)
        v,ran=self.suite.recheck(self.inputs,self.values,x)
        return self._edge(("observed",Evaluation(self.current,p,tuple(x.items()),tuple(v.items()),ran)))
    def construct(self, i):
        # A checked receipt selects exact predecessor, observations and cost.
        if type(i) is not int or not 0 <= i < len(self._edges):
            return None
        edge = self._edges[i]
        if edge[0]!="observed" or edge[1].predecessor != self.current:
            return None
        e=edge[1]; v=dict(e.values)
        allowed=all(v[k] in vals for k,vals in self.possible.items())
        carries=all(v[k]==self.values[k] for _,_,k in self.coords)
        return Progress(e.predecessor,i) if allowed and carries and improves(e.proposal.cost,self.cost) else None
    def frontier(self, ids):
        valid=[p for i in ids if (p:=self.construct(i)) is not None]
        def cost(p):return self._edges[p.report_id][1].proposal.cost
        out=[]
        for p in valid:
            if any(cost(q)!=cost(p) and improves(cost(q),cost(p)) for q in out):
                continue
            out=[q for q in out if not(cost(p)!=cost(q) and improves(cost(p),cost(q)))]
            out.append(p)
        return sorted(out,key=lambda p:(cost(p),self._edges[p.report_id][1].proposal.name,p.report_id))
    def publish(self, receipt):
        if receipt is None or self.construct(receipt.report_id)!=receipt:
            return False
        e=self._edges[receipt.report_id][1]
        self._edge(("progress",receipt))
        self.inputs,self.values,self.cost=dict(e.inputs),dict(e.values),e.proposal.cost
        return True

RULES=[Rule('qualified','stable',('setting',)),
       Rule('order-a','last',('forward',)),
       Rule('order-b','last',('backward',)),
       Rule('effect-a','effect',('order-a','left','right')),
       Rule('effect-b','effect',('order-b','left','right')),
       Rule('out-a','pair',('qualified','effect-a')),
       Rule('out-b','pair',('qualified','effect-b')),
       Rule('projection','pair',('out-a','out-b')),
       Rule('package','same',('setting',)),
       Rule('sign','pair',('package','signing')),
       Rule('manifest','pair',('sign','projection'))]
RULES+=[Rule(f'carried-{n}','same',('other',)) for n in range(32)]
INPUTS=dict(setting=200,forward=(0,1),backward=(1,0),left=0,right=0,other=0,signing=3)
SUITE=Suite(INPUTS,RULES)
COORD=((0,0,'out-a'),(0,1,'out-b'))
POSSIBLE={'qualified':(0,1),'effect-a':(0,1),'effect-b':(0,1)}

def new():
    return Ledger(SUITE,INPUTS,(10,10),COORD,POSSIBLE)
