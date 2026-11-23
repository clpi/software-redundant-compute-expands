from campaign import *

# Independent cold specification of the finite release fixture (not Suite.cold).
def oracle(x):
    q = int(1 <= x['setting'] <= 299)
    a = (q,(x['forward'][-1]+x['left']*x['right']) % 2)
    b = (q,(x['backward'][-1]+x['left']*x['right']) % 2)
    sig = x['setting'],x['signing']
    both = a,b
    return {'qualified':q,'order-a':x['forward'][-1],'order-b':x['backward'][-1],
            'effect-a':a[1],'effect-b':b[1],'out-a':a,'out-b':b,'projection':both,
            'package':x['setting'],'sign':sig,'manifest':(sig,both),
            **{f'carried-{i}':x['other'] for i in range(32)},**x}

rng=Random(20261123)
count=recalc=0
for trial in range(120):
    l = new()
    for step in range(8):
        ps=[]
        for i in range(9):
            edits=dict(setting=rng.choice([200,250,301]),left=rng.randrange(2),right=rng.randrange(2))
            if rng.randrange(4)==0: edits['forward']=tuple(reversed(l.inputs['forward']))
            if rng.randrange(4)==0: edits['signing']=rng.randrange(5)
            if rng.randrange(4)==0: edits['other']=rng.randrange(4)
            ps.append(Proposal(str(i),tuple(edits.items()),(rng.randrange(12),rng.randrange(12))))
        ids=[l.evaluate(p) for p in ps]
        ok=[]
        for i,p in zip(ids,ps):
            e=l.evidence[i][1]
            x=dict(l.inputs,**dict(p.edit))
            ref=oracle(x)
            assert dict(e.values)==ref
            want=(ref['out-a']==l.values['out-a'] and ref['out-b']==l.values['out-b']
                  and all(a<=b for a,b in zip(p.cost,l.cost)))
            assert (l.construct(i) is not None)==want
            if want:ok.append(i)
            count+=1;recalc+=len(e.recomputed)
        def dominated(i):
            x=l.evidence[i][1].proposal.cost
            return any(y!=x and y[0]<=x[0] and y[1]<=x[1]
                       for n in ok for y in (l.evidence[n][1].proposal.cost,))
        front=l.frontier(ids)
        assert {p.report_id for p in front}=={i for i in ok if not dominated(i)}
        old=l.evidence
        if front:
            w=front[0]
            assert l.publish(w)
            assert not l.publish(w) # stale same predecessor
            assert l.evidence[:-1]==old
        else:
            assert not l.publish(None) and l.evidence==old
l=new()
a=l.evaluate(Proposal('A',(('left',1),),(9,10)))
b=l.evaluate(Proposal('B',(('right',1),),(10,9)))
j=l.evaluate(Proposal('A+B',(('left',1),('right',1)),(8,8)))
assert l.construct(a) and l.construct(b) and l.construct(j) is None
assert l.evidence[j][0]=='observed' and l.current==0
c=l.evaluate(Proposal('config only',(('setting',250),),(9,9)))
e=l.evidence[c][1]
assert l.construct(c) is not None and set(e.recomputed)=={'qualified','package','sign','manifest'}
assert l.values['out-a']!=l.values['out-b']
print(f'{count} proposed states exact against independent cold model; {recalc} executions versus {count*len(RULES)} cold')
print('960 search rounds: exact exhaustive frontiers; no stale publication; prior evidence prefixes retained')
print('200→250: 4 executions of 43; 39 retained; both ordered observations unchanged')
print('A and B separately construct; A+B stays observable but cannot construct progress')
