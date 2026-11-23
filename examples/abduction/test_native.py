"""Replay small generated scopes in an actual pinned native Idol executable."""
import argparse, json, random, subprocess, tempfile
from pathlib import Path
from abduction import Ledger,Query
from native_fixture import emit
from check_abduction import replay

p=argparse.ArgumentParser()
p.add_argument('idol',type=Path); args=p.parse_args()
i=args.idol.resolve()
rng=random.Random(330)
root=Path(__file__).resolve().parent
inputs=[json.loads((root/'example.json').read_text())]
for case in range(15):
    syms=list('abcdefg')
    rs=[dict(id=str(j),kind='hypothesis',scope='z',head=rng.choice(syms),action=str(j)) for j in range(5)]
    rs.extend(dict(id='r'+str(j),kind='rule',scope='z',head=rng.choice(syms),
               premises=rng.choices(syms,k=rng.randrange(4))) for j in range(13))
    inputs.append(dict(records=rs,query=dict(scope='z',goals=rng.sample(syms,2),
        forbidden=rng.sample(syms,case%3),costs={str(j):[1,j] for j in range(5)},
        dimensions=['a','b']),weights=[1,1]))
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    for x in inputs:
        l=Ledger();l.append(x['records'])
        c=l.query(Query(**x['query']),x['weights'])
        assert replay(x['records'],x['query'],c,x['weights'])['verified']
        code,actions=emit(x)
        source=d/'native.id'
        source.write_text(code)
        binary=d/'native.out'
        subprocess.run([i,'compile','--no-cache','--backend','direct',source,'-o',binary],
                       check=True,capture_output=True,timeout=20)
        seen=subprocess.check_output([binary],text=True,timeout=20)
        actual={frozenset(a for j,a in enumerate(actions) if int(n)&(1<<j)) for n in seen.splitlines()}
        expected={frozenset(s['assumptions']) for s in c['supports']}
        assert actual==expected,(len(actions),actual,expected,x,code)
print(f'{len(inputs)}/{len(inputs)} emitted Idol binaries matched the checked explanation families')
