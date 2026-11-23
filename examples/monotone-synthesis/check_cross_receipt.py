"""Exact base -> generated replay using separately read expected input."""
import json
from pathlib import Path
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor

HOME = Path(__file__).resolve().parent
def command(name, *args, **kw):
    return subprocess.run([sys.executable, str(HOME / name), *map(str,args)],
                          capture_output=True, **kw)
def load(p):
    return json.loads(p.read_text())
def canonical(a):
    return json.dumps({k:v for k,v in a.items() if k != 'id'}, sort_keys=True)
def live(s):
    return {canonical(s['arts'][str(i)]) for i in s['live']}
def verify(a,b,original):
    assert a['reach']==b['reach'] and live(a)==live(b)
    assert (len(a['reach']),len(a['live']),len(a['pending']))==(329,330,0)
    assert a['log'][:len(original['log'])]==original['log']
    assert all(a['arts'][i]==art for i,art in original['arts'].items())
with tempfile.TemporaryDirectory() as d:
    work=Path(d)
    for label,stream in [('base','stream.jsonl'),('expanded','stream-gen.jsonl')]:
        command('loop.py', HOME/'receipts'/stream, '--emit-events', work/label, check=True)
    base,expanded=work/'base',work/'expanded'
    original,continued,cold=[work / n for n in ('original.json','continued.json','cold.json')]
    command('ingest.py', original, base, check=True)
    continued.write_bytes(original.read_bytes())
    command('ingest.py', continued, expanded, check=True)
    command('ingest.py', cold, expanded, check=True)
    a,b,s=map(load,(continued,cold,original))
    verify(a,b,s)
    evs=[json.loads(x) for x in expanded.read_text().splitlines()]
    rules=[e['art'] for e in evs if e['kind']=='offer'
           and e['art']['verdict']=='PASSED' and e['art']['observed'] in ('root','reached')]
    reach=set()
    while (ext:=reach|{r['head'] for r in rules if set(r['prem'])<=reach})!=reach:
        reach=ext
    assert set(a['reach'])==reach
    saved=continued.read_bytes()
    command('ingest.py',continued,expanded,check=True)
    assert continued.read_bytes()==saved
    e=evs[0]
    f=dict(e,art=dict(e['art'], head='bad:conflicting'))
    bad=work/'bad'
    bad.write_text(json.dumps(e)+'\n'+json.dumps(f)+'\n')
    fail=command('ingest.py',continued,bad)
    assert fail.returncode==1 and b'conflicting producer artifact ID' in fail.stderr
    assert continued.read_bytes()==saved
    for i in range(12):
        state=work/f'concurrent{i}.json'
        state.write_bytes(original.read_bytes())
        order=[base,expanded,base,expanded]
        order=order[i%4:]+order[:i%4]
        with ThreadPoolExecutor(max_workers=4) as pool:
            for f in [pool.submit(command,'ingest.py',state,p,check=True) for p in order]:
                f.result()
        verify(load(state),b,s)
print('PASS: 329 reachable, 330 live, 48 concurrent submissions, intact history and refusal')
