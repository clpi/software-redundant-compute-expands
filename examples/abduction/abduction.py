"""Exact, scoped, proof-producing abduction on the existing Horn projection."""
import argparse
from collections import defaultdict
from copy import deepcopy
from functools import lru_cache
from hashlib import sha256
import json
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parent.parent / "action-vector"))
from action_support import Edge, Supports, key, frontier, choose

def canonical(value):
    return json.dumps(value, separators=(",", ":"), sort_keys=True, allow_nan=False)

def digest(value):
    return sha256(canonical(value).encode()).hexdigest()

def check_schema(record):
    keys={"id","scope","kind","head"}
    if not isinstance(record,dict) or record.get("kind") not in ("fact","rule","hypothesis"):
        raise ValueError("unknown record kind")
    kind=record["kind"]
    extra={"fact":{"receipt"},"rule":{"premises"},"hypothesis":{"action"}}[kind]
    if set(record)!=keys|extra:
        raise ValueError("invalid record shape")
    for k in keys|({"receipt"} if kind=="fact" else {"action"} if kind=="hypothesis" else set()):
        if type(record[k]) is not str or not record[k]:
            raise ValueError("invalid symbolic ID")
    if kind=="rule" and (type(record["premises"]) is not list or
                         any(type(x) is not str or not x for x in record["premises"])):
        raise ValueError("invalid premise list")

def qualify(records, scope):
    rules={}
    witnesses=defaultdict(set)
    for r in records:
        if r["scope"]!=scope:continue
        if r["kind"]=="fact":
            rules[r["id"]]=Edge((),r["head"])
        elif r["kind"]=="rule":
            rules[r["id"]]=Edge(tuple(r["premises"]),r["head"])
        else:
            witnesses[r["action"]].add(r["head"])
    return rules,witnesses

def derive(rules, witnesses, allowed):
    """Cold witness reconstruction. Consume only selected assumptions."""
    trace={}
    for a in sorted(allowed):
        for s in sorted(witnesses[a]):
            trace.setdefault(s,("assumption",a))
    changed=True
    while changed:
        changed=False
        for i,e in sorted(rules.items()):
            if e.head not in trace and all(s in trace for s in e.premises):
                trace[e.head]=("rule",i)
                changed=True
    return trace

def cone(rules, ww, targets):
    """Backward reach for impact, not Horn inference."""
    incoming=defaultdict(list)
    for i,e in rules.items():incoming[e.head].append((i,e))
    live=set()
    need=set(targets)
    todo=list(need)
    while todo:
        for i,e in incoming[todo.pop()]:
            live.add(i)
            for p in e.premises:
                if p not in need:need.add(p);todo.append(p)
    return {i:e for i,e in rules.items() if i in live}, {a:hs&need for a,hs in ww.items() if hs&need}

class Query:
    def __init__(self, scope, goals, forbidden, costs, dimensions):
        if (type(scope) is not str or not scope or not goals or
                not isinstance(goals,(list,tuple)) or not isinstance(forbidden,(list,tuple)) or
                not isinstance(costs,dict) or not isinstance(dimensions,(list,tuple))):
            raise ValueError("query requires a scope and nonempty goal set")
        if any(type(x) is not str or not x for x in (*goals,*forbidden,*costs)):
            raise ValueError("invalid goal, blocker or action")
        self.scope=scope
        self.goals=frozenset(goals)
        self.forbidden=frozenset(forbidden)
        if not dimensions or len(set(dimensions))!=len(dimensions) or any(type(x) is not str or not x for x in dimensions):
            raise ValueError("invalid dimension schema")
        self.dimensions=tuple(dimensions)
        self.costs={a:tuple(v) for a,v in costs.items()}
        if any(len(v)!=len(dimensions) or any(type(x) is not int or x<0 for x in v)
               for v in self.costs.values()):
            raise ValueError("nonnegative exact cost vector required")
    def identity(self):
        return [self.scope,sorted(self.goals),sorted(self.forbidden),self.dimensions,self.costs]
    def cost(self,s):
        return tuple(sum(self.costs[a][i] for a in s) for i in range(len(self.dimensions)))

class Ledger:
    """An append-only record projection, not a writer or release authority."""
    def __init__(self):
        self._records={}
        self._indices={}
        self._projection_cache={}
    @property
    def records(self):
        return [json.loads(s) for s in self._records.values()]
    def append(self,records):
        incoming={}
        for r in records:
            check_schema(r)
            k,s=r["id"],canonical(r)
            if (k in self._records and self._records[k]!=s) or (k in incoming and incoming[k]!=s):
                raise ValueError("record ID reused with different contents")
            incoming[k]=s
        self._records.update(incoming)
    def query(self, query, weights):
        records = self.records
        rules, ww = qualify(records,query.scope)
        rules, ww = cone(rules,{a:s for a,s in ww.items() if a in query.costs},query.goals|query.forbidden)
        universe=tuple(sorted(ww,key=lambda a:(tuple(sorted(ww[a])),a)))
        assert set(universe)<=query.costs.keys()
        # Separate pure policy changes from graph and query changes.
        space=(query.scope,tuple(sorted(query.goals|query.forbidden)),tuple(sorted(query.costs)))
        idx, prior, seeds=self._indices.setdefault(space,(Supports(),set(),set()))
        ee=set(rules.values())
        ss={(h,a) for a,hs in ww.items() for h in hs}
        if not prior <= ee or not seeds <= ss:
            raise ValueError("nonappend projection")
        idx.append(ee-prior,ss-seeds)
        prior.update(ee);seeds.update(ss)
        bound=sorted((r for r in records if r["scope"]==query.scope and
                      (r["id"] in rules or (r["kind"]=="hypothesis" and
                       r["head"] in ww.get(r["action"],set())))),key=lambda r:r["id"])
        hasher=digest([bound,sorted((i,e.premises,e.head) for i,e in rules.items()),
                       sorted((a,sorted(hs)) for a,hs in ww.items()),query.identity()])
        state=self._projection_cache.get(hasher)
        same=state is not None
        if state is None:
            @lru_cache(None)
            def cold(s):return derive(rules,ww,s)
            valid=[]
            for s in idx.require_all(sorted(query.goals)):
                t=cold(s)
                if query.goals<=t.keys() and not query.forbidden & t.keys():
                    # A positive certificate never confers an observed status.
                    valid.append((s,tuple((x,*w) for x,w in t.items())))
            ord_goals=tuple(sorted(query.goals))
            bounds=[0]
            def cover(lo,i):
                bounds[0]+=1
                for j,(s,_) in enumerate(valid):
                    if s<=lo:return ["covered",j]
                no=cold(lo)
                if query.forbidden & no.keys():
                    return ["forbidden",sorted(query.forbidden & no.keys())[0]]
                hi=lo|frozenset(universe[i:])
                missing=query.goals-cold(hi).keys()
                if missing:return ["unreachable",next(g for g in ord_goals if g in missing)]
                if i==len(universe):raise ValueError("incomplete support family")
                return ["split",universe[i],cover(lo,i+1),cover(lo|{universe[i]},i+1)]
            certificate=cover(frozenset(),0)
            state=(valid,certificate,idx.evaluations,bounds[0])
            self._projection_cache[hasher]=state
        valid,certificate,evaluations,boxes=state
        pareto=frontier((p for p,_ in valid),query.cost)
        winner=choose(pareto,tuple(weights))
        return {"kind":"hypothetical-not-authority","projection":hasher,
                "universe":list(universe),"axes":list(query.dimensions),"weights":list(weights),
                "supports":[{"assumptions":list(key(s)),"proof":[list(row) for row in p]}
                            for s,p in valid],
                "cover":deepcopy(certificate),"frontier":[[list(key(s)),list(v)] for s,v in pareto],
                "selected":None if winner is None else list(key(winner[0])),
                "work":{"ruleEvaluationsTotal":evaluations,"coverNodes":boxes,"projectionReused":same}}

def read_input(path):
    with open(path) as f:
        return json.load(f)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("input")
    args=ap.parse_args()
    x=read_input(args.input)
    l=Ledger()
    l.append(x["records"])
    q=Query(**x["query"])
    print(canonical(l.query(q,x["weights"])))

if __name__=="__main__":main()
