"""Independent exact checker: no support-index, pruning, or planner dependency."""
import argparse
from hashlib import sha256
import json

def need(ok, error):
    if not ok: raise ValueError(error)

def replay(raw, query, cert, weights, *, _return_policy=False):
    byid={}
    for r in raw:
        i=r['id']
        need(i not in byid or byid[i]==r,'conflicting source record')
        byid[i]=r
    goals, forbid = set(query['goals']),set(query['forbidden'])
    costs,axes=query['costs'],query['dimensions']
    scope=query['scope']
    need(goals and axes and len(axes)==len(set(axes)),'empty or duplicate query axis')
    need(all(len(xs)==len(axes) and all(type(v) is int and v>=0 for v in xs)
             for xs in costs.values()),'cost schema')
    need(cert['kind']=='hypothetical-not-authority' and cert['weights']==weights
         and cert['axes']==axes and len(weights)==len(axes)
         and all(type(w) is int and w>=0 for w in weights),'wrong query policy')
    edges, hy = {}, {}
    for i,r in byid.items():
        if r['scope']!=scope:continue
        if r['kind']=='hypothesis':
            if r['action'] in costs:
                hy.setdefault(r['action'],set()).add(r['head'])
        elif r['kind']=='rule':
            edges[i]=(r['premises'],r['head'])
        else:
            need(r['kind']=='fact' and r['receipt'],'invalid declared fact')
            edges[i]=([],r['head'])
    # Independent saturating backward projection. Outside it no rule into the
    # slice can see those assumptions; omission is not a claimed observation.
    slice_=goals|forbid
    while True:
        n=slice_|{p for ps,h in edges.values() if h in slice_ for p in ps}
        if n==slice_:break
        slice_=n
    relevant=tuple(sorted((a for a,hs in hy.items() if hs&slice_),
                          key=lambda x:(tuple(sorted(hy[x]&slice_)),x)))
    need(relevant==tuple(cert['universe']),'wrong universe')
    bound=[r for i,r in sorted(byid.items()) if r["scope"]==scope and
           ((i in edges and edges[i][1] in slice_) or
            (r["kind"]=="hypothesis" and r["action"] in relevant and r["head"] in slice_))]
    projection=[bound,sorted((i,ps,h) for i,(ps,h) in edges.items() if h in slice_),
                sorted((a,sorted(hy[a]&slice_)) for a in relevant),
                [scope,sorted(goals),sorted(forbid),axes,costs]]
    binding=sha256(json.dumps(projection,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    need(cert['projection']==binding,'stale projection')
    cache={}
    def closure(s):
        if s in cache:return cache[s]
        cur={h for a in s for h in hy[a]}
        while True:
            n=cur|{h for ps,h in edges.values() if all(p in cur for p in ps)}
            if n==cur:
                cache[s]=cur
                return cur
            cur=n
    plans=[]
    for support in cert['supports']:
        raw_s=support['assumptions']; s=frozenset(raw_s)
        need(raw_s==sorted(s) and s<=set(relevant) and s not in plans,'bad assumptions')
        known=set()
        for h,kind,ident in support['proof']:
            need(h not in known,'duplicate proof step')
            if kind=='assumption':
                need(ident in s and h in hy[ident],'unselected assumption')
            else:
                need(kind=='rule' and ident in edges,'unrecognized proof rule')
                ps,out=edges[ident]
                need(h==out and all(p in known for p in ps),'unfounded inference')
            known.add(h)
        need(goals<=known and not forbid&closure(s),'invalid explanation')
        need(all(not goals<=closure(s-{x}) for x in s),'not inclusion minimal')
        plans.append(s)
    def cover(branch,i,lo):
        k=branch[0]
        if k=='covered':
            need(len(branch)==2 and type(branch[1]) is int and 0<=branch[1]<len(plans)
                 and plans[branch[1]]<=lo,'bad coverage leaf')
        elif k=='forbidden':
            need(len(branch)==2 and branch[1] in forbid&closure(lo),'bad forbidden leaf')
        elif k=='unreachable':
            hi=lo|set(relevant[i:])
            need(len(branch)==2 and branch[1] in goals-closure(frozenset(hi)),'bad unreachable leaf')
        else:
            need(k=='split' and len(branch)==4 and i<len(relevant)
                 and branch[1]==relevant[i],'bad or incomplete decision split')
            cover(branch[2],i+1,lo)
            cover(branch[3],i+1,lo|{relevant[i]})
    cover(cert['cover'],0,frozenset())
    def cost(s):
        return [sum(costs[a][i] for a in s) for i in range(len(axes))]
    pairs=sorted([[sorted(s),cost(s)] for s in plans])
    # Lexicographic order places every strict componentwise dominator first.
    # Retaining only earlier nondominated vectors is valid by transitivity.
    live=[]
    for vector in sorted({tuple(v) for _,v in pairs}):
        if not any(all(x<=y for x,y in zip(prior,vector)) for prior in live):
            live.append(vector)
    live_set=set(live)
    right=[p for p in pairs if tuple(p[1]) in live_set]
    need(cert['frontier']==right,'wrong Pareto front')
    win=min(right,key=lambda p:(sum(x*y for x,y in zip(p[1],weights)),p[0]))[0] if right else None
    need(cert['selected']==win,'wrong policy winner')
    report={"verified":True,"supports":len(plans),"nondominated":len(right),"authority":False}
    if not _return_policy:return report
    # Only immutable values verified by the cold replay enter the handle.
    representatives={}
    for p,v in right: representatives.setdefault(tuple(v),tuple(p))
    frozen=tuple((p,v) for v,p in representatives.items())
    def verify(update):
        need(set(update)=={'projection','axes','weights','selected'},'invalid policy update')
        ws=update['weights']
        need(update['projection']==binding and tuple(update['axes'])==axis_key
            and type(ws) is list and len(ws)==len(axis_key)
            and all(type(w) is int and w>=0 for w in ws),'wrong checked snapshot or policy')
        best=min(frozen,key=lambda row:(sum(x*y for x,y in zip(ws,row[1])),row[0])) if frozen else None
        need(update['selected']==(list(best[0]) if best is not None else None),'wrong policy winner')
        return {**report,"projection":binding}
    axis_key=tuple(axes)
    return report,verify

def cli():
    ap=argparse.ArgumentParser()
    ap.add_argument('input')
    ap.add_argument('certificate')
    a=ap.parse_args()
    with open(a.input) as f:d=json.load(f)
    with open(a.certificate) as f:c=json.load(f)
    print(json.dumps(replay(d['records'],d['query'],c,d['weights']),sort_keys=True))
if __name__=='__main__':cli()
