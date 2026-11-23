"""Independent policy oracle and instrumentation of the no-replay path."""
from copy import deepcopy
from itertools import product
from unittest.mock import patch

import abduction as a
from check_abduction import replay

def fail(fn):
    try: fn()
    except ValueError: return
    raise AssertionError("bad policy accepted")

def hypothesis(name, head="done"):
    return dict(id="h:"+name,scope="p",kind="hypothesis",head=head,action=name)

source=[hypothesis(x) for x in ("a","b","c","d","e")]
raw=dict(scope="p",goals=["done"],forbidden=[],
         dimensions=["time","storage"],costs=dict(a=[1,7],b=[7,1],c=[5,5],d=[1,7],e=[8,8]))
ledger=a.Ledger()
ledger.append(source)
query=a.Query(**raw)
model,reused=ledger.prepare(query)
assert not reused
cert=model.certificate([1,1])
assert [p for p,_ in cert['frontier']]==[['a'],['b'],['c'],['d']]
report,verify=replay(source,raw,cert,[1,1],_return_policy=True)
assert report==dict(verified=True,supports=5,nondominated=4,authority=False)
assert model.reweight([1,0])['selected']==['a']
assert model.reweight([0,1])['selected']==['b']
assert model.reweight([0,0])['selected']==['a']
with patch.object(a.Ledger,'records',new_callable=lambda:property(
        lambda _: (_ for _ in ()).throw(AssertionError('source scanned')))), \
     patch.object(a,'derive',side_effect=AssertionError('closure replayed')), \
     patch.object(a,'digest',side_effect=AssertionError('projection rehashed')):
    for w in map(list,product(range(64),repeat=2)):
        state,hit=ledger.prepare(query)
        assert hit and state is model
        u=state.reweight(w)
        expected=min((sum(x*y for x,y in zip(w,raw['costs'][k])),k) for k in ('a','b','c','d'))[1]
        assert u['selected']==[expected] and verify(u)['authority'] is False
for wrong in [dict(selected=['d']),dict(projection='wrong'),dict(axes=['storage','time']),
              dict(weights=[True,0]),dict(weights=[-1,1]),dict(authority=True)]:
    changed={**model.reweight([1,0]),**wrong}
    fail(lambda:verify(changed))
# Canonical winner must come from the front, even with zero weights.
with_cheap_outside=deepcopy(raw)
with_cheap_outside['costs']['a']=[9,9]
new=ledger.prepare(a.Query(**with_cheap_outside))[0]
fail(lambda:verify(new.reweight([0,0])))
changed_axes={**raw,'dimensions':['storage','time']}
fail(lambda:verify(ledger.prepare(a.Query(**changed_axes))[0].reweight([0,0])))
ledger.append([hypothesis('ignored','alien')])
assert ledger.prepare(query)[0] is model
ledger.append([dict(id='contradiction',scope='p',kind='fact',head='done',receipt='declared test')])
new=ledger.prepare(query)[0]
assert new.reweight([1,0])['selected']==[]
fail(lambda:verify(new.reweight([1,0])))
assert verify(model.reweight([1,0]))['projection']==model.projection
print('4096 policies, genuine winner flip, non-exposed undominated vector, all ties retained, 8 rejection controls, no source/closure/digest on weight-only path')
