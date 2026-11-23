"""Lower one finite graph to an executable Idol subset-search oracle."""
import argparse
from pathlib import Path
from abduction import Ledger,Query,qualify,cone,read_input

def emit(d):
    l=Ledger();l.append(d['records'])
    q=Query(**d['query'])
    edges,hyp=qualify(l.records,q.scope)
    edges,hyp=cone(edges,{a:h for a,h in hyp.items() if a in q.costs},q.goals|q.forbidden)
    atoms=sorted(set(q.goals)|set(q.forbidden)|{s for e in edges.values() for s in (*e.premises,e.head)}
                 |set().union(*hyp.values()))
    acts=sorted(hyp)
    if len(atoms)>62 or len(acts)>20:raise ValueError('outside native fixture width')
    n={x:1<<i for i,x in enumerate(atoms)}
    def mask(xs):
        return sum(n[x] for x in set(xs))
    p=['onepass: i64 = (facts: i64)', '    have: i64 = facts']
    for e in sorted(set(edges.values())):
        if not e.premises:
            p.append(f'    have = have | {n[e.head]}')
        else:
            val=mask(e.premises)
            p.extend((f'    if (have & {val}) == {val}',f'        have = have | {n[e.head]}'))
    p.extend(('    have','','closure: i64 = (facts: i64)', '    have: i64 = facts'))
    p.extend('    have = onepass(have)' for _ in atoms)
    p.extend(('    have','', 'solves: bool = (pick: i64)','    initial: i64 = 0'))
    for i,a in enumerate(acts):
        val=mask(hyp[a])
        p.extend((f'    if (pick & {1<<i}) != 0',f'        initial = initial | {val}'))
    goal,bad=mask(q.goals),mask(q.forbidden)
    p.extend(('    result: i64 = closure(initial)',f'    (result & {goal}) == {goal} and (result & {bad}) == 0','',
            'main: i64 = ()','    pick: i64 = 0', f'    while pick < {1<<len(acts)}',
            '        if solves(pick)','            minimal: bool = true','            bit: i64 = 1',
            f'            while bit < {1<<len(acts)}','                if (pick & bit) != 0 and solves(pick - bit)',
            '                    minimal = false','                bit = bit + bit','            if minimal',
            '                print(pick)','        pick = pick + 1','    0','','os.exit(main())',''))
    return '\n'.join(p), acts

if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument('input')
    ap.add_argument('source',type=Path)
    a=ap.parse_args()
    code,acts=emit(read_input(a.input))
    a.source.write_text(code)
    print('\n'.join(acts))
