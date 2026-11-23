from abduction import Ledger,Query
from check_abduction import replay
from copy import deepcopy
from itertools import combinations
from random import Random

def rec(i,kind,head,scope="test",**kw):
    return dict(id=str(i),kind=kind,head=head,scope=scope,**kw)
def q(goals,forbidden,costs):
    return dict(scope="test",goals=goals,forbidden=forbidden,costs=costs,dimensions=["wait","compute"])
def target(records,query,weights=(1,1)):
    l=Ledger();l.append(records);x=l.query(Query(**query),list(weights))
    assert replay(records,query,x,list(weights))['verified']
    return x

def independent(records,qq):
    rr=[r for r in records if r['scope']==qq['scope']]
    acts=list(qq['costs']);sol=[]
    for n in range(len(acts)+1):
      for tup in combinations(acts,n):
        s=frozenset(tup)
        if any(p<s for p in sol):continue
        have={r['head'] for r in rr if r['kind']=='fact' or
              (r['kind']=='hypothesis' and r['action'] in s)}
        # independent finite iteration bound: each nonterminal round adds a head
        for _ in range(len(rr)+1):
            have=have|{r['head'] for r in rr if r['kind']=='rule' and set(r['premises'])<=have}
        if set(qq['goals'])<=have and not have.intersection(qq['forbidden']):
            sol.append(s)
    return set(sol)

rng=Random(470)
trials=0
for tx in range(72):
    l=Ledger(); n=5; universe=[str(i) for i in range(n)]
    syms=list('abcdefgh')
    record=[rec(i,"hypothesis",rng.choice(syms),action=a) for i,a in enumerate(universe)]
    record.extend(rec(6+i,"rule",rng.choice(syms),premises=rng.choices(syms,k=rng.randrange(4))) for i in range(16))
    record.append(rec(99,"fact","a","different",receipt="unrelated"))
    qq=q(rng.sample(syms,rng.randrange(1,4)),rng.sample(syms,rng.randrange(3)),
         {i:[rng.randrange(6),rng.randrange(6)] for i in universe})
    st=Query(**qq)
    prior=0
    for cuts in (5,9,13,18,len(record)):
        l.append(record[prior:cuts]);prior=cuts
        x=l.query(st,[2,1])
        assert replay(l.records,qq,x,[2,1])['verified']
        assert {frozenset(a['assumptions']) for a in x['supports']}==independent(record[:cuts],qq)
        y=l.query(st,[1,3])
        assert y['work']['projectionReused'] and y['frontier']==x['frontier']
        assert replay(l.records,qq,y,[1,3])['verified']
        trials+=1

# Exact release-shaped example: independently observed trusted inputs are
# data in this fixture; adding a hypothesized missing result is not promotion.
records=[rec(0,'fact','same-toolchain',receipt='fixture:toolchain:exact'),
         rec(1,'fact','artifact-b-unchanged',receipt='fixture:b:exact'),
         rec(2,'hypothesis','hardware-replayed',action='bench'),
         rec(3,'hypothesis','hardware-replayed',action='reuse'),
         rec(4,'hypothesis','order-b-replayed',action='reorder'),
         rec(5,'hypothesis','order-b-replayed',action='bench'),
         rec(6,'rule','release-obligations-met',premises=['same-toolchain','artifact-b-unchanged','hardware-replayed','order-b-replayed']),
         rec(7,'rule','forbidden-reordering',premises=['order-b-replayed','fast-path']),
         rec(8,'hypothesis','fast-path',action='reorder')]
qq=q(['release-obligations-met'],['forbidden-reordering'],{'bench':[5,1],'reuse':[1,5],'reorder':[1,1]})
c=target(records,qq)
assert c['selected']==['bench'] and len(c['supports'])==1
assert not independent(records,q(qq['goals'],qq['forbidden'],{}))

def refused(data,cert):
    try: replay(data,qq,cert,[1,1])
    except (ValueError,KeyError,TypeError): return
    raise AssertionError('accepted mutated certificate')
x=deepcopy(c);x['supports'][0]['proof'][-1][1]='assumption';refused(records,x)
x=deepcopy(c);x['cover']=['covered',0];refused(records,x)
x=deepcopy(c);x['supports']=[];refused(records,x)
x=deepcopy(c);x['frontier']=[];refused(records,x)
x=deepcopy(c);x['kind']='authority';refused(records,x)
changed=deepcopy(records);changed[0]['receipt']='wrong extracted source';refused(changed,c)
# A grounded contradiction invalidates old hypothetical plans; it is not a
# new fact inferred from the hypothetical branch.
grounded=records+[rec(12,'fact','forbidden-reordering',receipt='fixture:counterexample')]
refused(grounded,c)
assert not target(grounded,qq)['supports']
# Current facts may refute one explanation without refuting another.
order=[rec('h1','hypothesis','commutes',action='assume'),
       rec('h2','hypothesis','fresh-trace',action='measure'),
       rec('r1','rule','joint-check',premises=['commutes']),
       rec('r2','rule','joint-check',premises=['fresh-trace']),
       rec('r3','rule','conflict',premises=['commutes','alias'])]
oq=q(['joint-check'],['conflict'],{'assume':[1,1],'measure':[2,2]})
o=Ledger();o.append(order)
old=o.query(Query(**oq),[1,1])
assert {tuple(s['assumptions']) for s in old['supports']}=={('assume',),('measure',)}
o.append([rec('new','fact','alias',receipt='qualified shared alias')])
new=o.query(Query(**oq),[1,1])
assert new['selected']==['measure'] and replay(o.records,oq,new,[1,1])['verified']
try: replay(o.records,oq,old,[1,1])
except ValueError: pass
else: raise AssertionError('allowed stale explanation after observed alias')
# Coarse terms cannot stand in for exact term identity merely because a view
# assigned the same class. No checked cross-resolution transport was provided.
exact=[rec('k1','fact','10',receipt='exact atom'),
       rec('k2','rule','99',premises=['11']),
       rec('k3','fact','99','coarse',receipt='projected derivation')]
assert not target(exact,q(['99'],[],{}))['supports']
# 20 actions arranged into 10 independent necessary choices; checker has an
# explicit frontier rather than assuming that candidate enumeration is complete.
large=[rec(i,'hypothesis',str(i//2),action=str(i)) for i in range(20)]
big=q([str(i) for i in range(10)],[],{str(i):[1,1] for i in range(20)})
bigc=target(large,big)
assert len(bigc['supports'])==1024
print(f'{trials} growing prefixes matched independent powerset search and reweighting')
print('7 altered proof, authority or projection cases refused; grounded blocker cancels hypothesis')
print('10 independent binary obligations: 1024 exact minimal supports and a checked finite cover')
print(f'cover nodes: {bigc["work"]["coverNodes"]}; raw subsets: {1<<20}')
