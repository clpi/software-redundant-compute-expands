#!/usr/bin/env python3
"""Offline toy UI graph; exact Pareto and incremental audit. No browser or OS actions."""
from collections import Counter, defaultdict
from dataclasses import dataclass
from hashlib import sha256
import itertools
import json
import random


@dataclass(frozen=True)
class Action:
    id: str
    src: int
    dst: int
    cost: tuple[int, int, int]  # latency units, risk units, interactions
    evidence: str             # explicit, checked, label-only, stale, wrong-effect
    revision: int = 1
    expected_effect: str = "safe-preview"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def qualifies(a, revision=1):
    return (a.evidence in {"explicit","checked"} and a.revision==revision and
            a.expected_effect=="safe-preview" and a.src<a.dst and
            len(a.cost)==3 and all(type(x) is int and x>=0 for x in a.cost))


def plus(a,b):
    return tuple(x+y for x,y in zip(a,b))


def dominates(a,b):
    return a!=b and all(x<=y for x,y in zip(a,b))


def frontier(labels):
    """Keep one deterministic path (lexical IDs) per nondominated vector."""
    costs={}
    for cost,path in labels:
        costs[cost]=min(path,costs.get(cost,path))
    return tuple(sorted((v,p) for v,p in costs.items()
                        if not any(dominates(w,v) for w in costs)))


def exhaustive(actions,n):
    successors=defaultdict(list)
    for a in actions:
        require(type(a.src) is int and 0<=a.src<a.dst<n,"invalid graph")
        successors[a.src].append(a)
    terminals=[]
    expanded=0
    def visit(state,cost,trace):
        nonlocal expanded
        if state==n-1:
            terminals.append((cost,trace))
            return
        for a in successors[state]:
            expanded+=1
            visit(a.dst,plus(cost,a.cost),trace+(a.id,))
    visit(0,(0,0,0),())
    # Independent pairwise filter on completed paths.
    exact=tuple(sorted({(v,min(u for w,u in terminals if w==v))
                        for v,p in terminals if not any(
                            v!=w and all(a<=b for a,b in zip(w,v)) for w,u in terminals)}))
    return exact,expanded,len(terminals)


class Incremental:
    def __init__(self,n):
        self.n=n
        self.actions={}
        self.labels=[() for i in range(n)]
        self.labels[0]=(((0,0,0),()),)
    def update(self,add=(),remove=()):
        touched=set()
        trial=dict(self.actions)
        for key in remove:
            a=trial.pop(key)
            touched.add(a.dst)
        for a in add:
            require(qualifies(a) and a.id not in trial,"unqualified/duplicate action")
            require(0<=a.src<a.dst<self.n,"invalid edge")
            trial[a.id]=a
            touched.add(a.dst)
        self.actions=trial
        incoming=defaultdict(list)
        outgoing=defaultdict(set)
        for a in self.actions.values():
            incoming[a.dst].append(a)
            outgoing[a.src].add(a.dst)
        work=0
        evaluated=0
        for q in range(1,self.n):
            if q not in touched:
                continue
            evaluated+=1
            candidates=[]
            for a in incoming[q]:
                for cost,trace in self.labels[a.src]:
                    work+=1
                    candidates.append((plus(a.cost,cost),trace+(a.id,)))
            revised=frontier(candidates)
            if revised!=self.labels[q]:
                touched.update(outgoing[q])
                self.labels[q]=revised
        return self.labels[-1],work,evaluated


def fixture(seed):
    r=random.Random(seed)
    n=10
    explicit=[Action(f"nav{i}",i,i+1,(r.randint(5,12),r.randint(0,3),1),
                     "explicit") for i in range(n-1)]
    checked=[]
    for a,b in itertools.combinations(range(n),2):
        if b-a>1 and r.random()<0.21:
            checked.append(Action(f"route{a:02}-{b:02}",a,b,
                                  (r.randint(4,24),r.randint(0,6),1),"checked"))
    r.shuffle(checked)
    decoys=[
        Action("proposed-lock",0,n-1,(0,0,0),"wrong-effect",expected_effect="unrequested-change"),
        Action("proposed-copy",0,n-1,(1,0,1),"stale",revision=0),
        Action("proposed-label",0,n-1,(1,0,1),"label-only"),
    ]
    return n,explicit,checked,decoys


def run(n,explicit,checked,decoys):
    acc=Counter()
    state=Incremental(n)
    cut=(len(checked)+1)//2
    # Two append batches, then removal of the first caught stale action,
    # then a fully checked restoration (same action identity and revision).
    withdraw=tuple(a.id for a in checked[:1])
    epochs=[(explicit,()),(checked[:cut],()),(checked[cut:],()),
            ([],withdraw),(checked[:1],())]
    all_explicit=exhaustive(explicit,n)[0]
    checked_by={a.id:a for a in checked}
    known={a.id:a for a in explicit+checked+decoys}
    result=[]
    for i,(add,remove) in enumerate(epochs):
        retained,work,evaluated=state.update(add,remove)
        oracle,xwork,xpaths=exhaustive(list(state.actions.values()),n)
        require(oracle==retained,"Pareto frontier mismatch")
        require(all(qualifies(known[k]) for v,p in retained for k in p),"invalid frontier")
        fresh=Incremental(n)
        optimal,dwork,deval=fresh.update(list(state.actions.values()))
        require(optimal==retained,"cold Pareto mismatch")
        # Proposal-only strips the explicit navigation; no evidence filter.
        # Hybrid starts from explicit navigation and admits only qualified proposals.
        available=[a for a in state.actions.values() if a.id in checked_by]
        unsafe,_,_=exhaustive(available+decoys,n)
        proposed_checked,_,_=exhaustive([a for a in available+decoys if qualifies(a)],n)
        false=sum(any(not qualifies(known[k]) for k in p) for v,p in unsafe)
        acc.update({
            "epochs":1, "wrong_proposed_frontier_labels":false,
            "proposed_unsafe_epochs":int(false>0),"hybrid_unsafe_labels":0,
            "explicit_feasible_epochs":int(bool(all_explicit)),
            "checked_proposed_feasible_epochs":int(bool(proposed_checked)),
            "hybrid_feasible_epochs":int(bool(retained)),
            "checked_proposed_illegal_labels":sum(
                any(not qualifies(known[k]) for k in p) for v,p in proposed_checked),
            "incremental_relaxations":work,"incremental_states":evaluated,
            "cold_dynamic_relaxations":dwork,"cold_dynamic_states":deval,
            "exhaustive_edge_visits":xwork,"exhaustive_goal_paths":xpaths,
            "incremental_relaxation_loss_epochs":int(work>dwork),
            "incremental_relaxation_win_epochs":int(work<dwork),
            "incremental_relaxation_tie_epochs":int(work==dwork),
            "hybrid_has_strict_latency_win":int(min(v[0] for v,p in retained)
                                                <min(v[0] for v,p in all_explicit)),
            "multiple_hybrid_pareto_points":int(len(retained)>1),
        })
        result.append({"epoch":i,"frontier":[[list(v),list(p)] for v,p in retained],
                       "retained_relaxations":work,"cold_relaxations":dwork})
    return acc,result


def counterexamples():
    # Lexicographic latency seeker: incumbent (9,0,1) meets a supposedly
    # "good enough" threshold 10; unseen continuation (2,0,2) is faster.
    a=[Action("direct",0,2,(9,0,1),"explicit"),
       Action("partial",0,1,(1,0,1),"checked"),
       Action("complete",1,2,(1,0,1),"checked")]
    exact=exhaustive(a,3)[0]
    require(min(v[0] for v,p in exact)==2 and len(exact)==2,"threshold fixture drift")
    # Every unfinished branch has nonnegative suffix cost. An incumbent
    # may settle the latency scalar only when no pending lower bound is
    # smaller. Missing rows require coverage bounds or an unknown result.
    pending_latency_bound=1
    require(pending_latency_bound < 9 <= 10,"threshold cannot prove optimality")
    # Feasible nondominated but unsupported point; nonnegative objective
    # weights over the first two axes with at least one positive cannot
    # select (2,3), because the midpoint of (0,4) and (4,0) is (2,2).
    v=[(0,4,1),(2,3,1),(4,0,1)]
    require(len(frontier((x,(str(i),)) for i,x in enumerate(v)))==3,"bad Pareto trade-off")
    clean=Incremental(3)
    clean.update(a)
    before=(dict(clean.actions),tuple(clean.labels))
    rejected=0
    for decoy in fixture(0)[3]:
        try:
            clean.update([decoy],["direct"])
        except ValueError:
            rejected+=1
        else:
            raise ValueError("decoy accepted")
        require(before==(clean.actions,tuple(clean.labels)),"refused update changed state")
    require(rejected==3,"missing decoy control")
    return {"unqualified_updates_refused_atomically":rejected,"threshold":10,"first_candidate_latency":9,
            "pending_latency_lower_bound":pending_latency_bound,
            "certified_minimum_latency":2,"full_pareto":exact,
            "unsupported_pareto_vectors":v,
            "unsupported_vector":v[1],
            "unsupported_note":"The middle point is not even a tied optimum for nonnegative latency and risk weights unless both are zero."}


if __name__=="__main__":
    totals=Counter()
    trials=[]
    for seed in range(32):
        acc,res=run(*fixture(seed))
        totals.update(acc)
        trials.append({"seed":seed,"metrics":dict(acc),"results":res})
    x={"kind":"synthetic no-browser action fixtures","trials":32,"measured_totals":dict(totals),
       "controls":counterexamples(),"cases":trials}
    print(json.dumps(x,indent=2,sort_keys=True))
