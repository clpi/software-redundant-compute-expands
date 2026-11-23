"""Report raw timings; baseline is a preceding abduction.py module at --baseline."""
import argparse, importlib.util, json, platform
from time import perf_counter_ns
import abduction as new
from check_abduction import replay

def main():
    args=argparse.ArgumentParser()
    args.add_argument('--baseline',required=True)
    args.add_argument('--repeat',type=int,default=7)
    ns=args.parse_args()
    spec=importlib.util.spec_from_file_location('old',ns.baseline)
    old=importlib.util.module_from_spec(spec); spec.loader.exec_module(old)
    records=[dict(id=str(i),scope='p',kind='hypothesis',action=str(i),head=str(i//2))
             for i in range(20)]
    q=dict(scope='p',goals=list(map(str,range(10))),forbidden=[],
           dimensions=['time','storage'],costs={str(i):[1,1] for i in range(20)})
    base, fast = old.Ledger(),new.Ledger()
    base.append(records); fast.append(records)
    oldq,newq=old.Query(**q),new.Query(**q)
    prepared,_=fast.prepare(newq)
    full=prepared.certificate([1,1])
    _,check=replay(records,q,full,[1,1],_return_policy=True)
    oldcert=base.query(oldq,[1,1])
    assert {k:v for k,v in full.items() if k!='work'}=={k:v for k,v in oldcert.items() if k!='work'}
    rows=[]
    for i in range(ns.repeat):
        w=[i+1,2*i+1]
        def cold():
            x=base.query(oldq,w)
            return {k:x[k] for k in ['projection','axes','weights','selected']}
        def hot():
            p,hit=fast.prepare(newq)
            assert hit
            u=p.reweight(w); check(u)
            return u
        got={}
        for name,f in ([('old',cold),('new',hot)] if i%2==0 else [('new',hot),('old',cold)]):
            t=perf_counter_ns(); out=f(); elapsed=perf_counter_ns()-t
            got[name]=(out,elapsed)
        assert got['old'][0]==got['new'][0]
        rows.append([w,got['old'][1],got['new'][1]])
    print(json.dumps(dict(python=platform.python_version(),system=platform.system(),
         machine=platform.machine(),supports=len(prepared.supports),
         retained_ties=len(prepared.front),representatives=len(prepared.representatives),
         old_dominance_checks_per_request=1024**2,new_checks_per_request=0,
         columns=['weights','old_plan_full_certificate_ns','new_prepare_choose_check_ns'],rows=rows),
         sort_keys=True))
if __name__=='__main__':main()
