"""Construct abductions from the actual merged #12 continuation discrepancy."""
import argparse
import json
from pathlib import Path
from subprocess import run
import sys
from tempfile import TemporaryDirectory
from abduction import Ledger,Query
from check_abduction import replay

def fixture(source):
    with TemporaryDirectory() as folder:
        lab=Path(folder)
        def cmd(path,*args):
            run([sys.executable,str(source/path),*map(str,args)],check=True,capture_output=True)
        for name,stream in [("base","stream.jsonl"),("expanded","stream-gen.jsonl")]:
            cmd("loop.py",source/"receipts"/stream,"--emit-events",lab/name)
        cmd("ingest.py",lab/"warm.json",lab/"base")
        cmd("ingest.py",lab/"warm.json",lab/"expanded")
        cmd("ingest.py",lab/"cold.json",lab/"expanded")
        warm,cold=[json.loads((lab/(s+".json")).read_text()) for s in ("warm","cold")]
    missing=set(cold["reach"])-set(warm["reach"])
    absent={i for i,v in cold["pool"].items() if v not in warm["pool"].values()}
    assert (len(warm["reach"]),len(cold["reach"]),len(missing),len(absent))==(321,329,8,3)
    scope="merged-12-receipt-recovery"
    def rec(i,k,h,**kw):return dict(id=i,kind=k,scope=scope,head=h,**kw)
    records=[rec("ledger:"+i,"rule",h,premises=ps) for i,(h,ps) in warm["pool"].items()]
    costs={"recover-index":[3,4]}
    for i in sorted(absent):
        h,ps=cold["pool"][i]
        action="reverify:"+h
        costs[action]=[3,1]
        assumption="restored:"+i
        records.extend([rec("oracle:"+i,"rule",h,premises=[*ps,assumption]),
                        rec("offer:"+i,"hypothesis",assumption,action=action),
                        rec("joined:"+i,"hypothesis",assumption,action="recover-index")])
    return {"records":records,"query":dict(scope=scope,goals=sorted(missing),forbidden=[],
            dimensions=["modeled-wait","modeled-compute"],costs=costs),"weights":[1,1]}

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--example-dir",type=Path,default=Path(__file__).resolve().parent.parent/"monotone-synthesis")
    ap.add_argument("--emit-input",action="store_true")
    a=ap.parse_args()
    x=fixture(a.example_dir.resolve())
    if a.emit_input:
        print(json.dumps(x,sort_keys=True))
    else:
        l=Ledger();l.append(x["records"])
        c=l.query(Query(**x["query"]),x["weights"])
        v=replay(x["records"],x["query"],c,x["weights"])
        assert v["supports"]==v["nondominated"]==2
        # The actual missing eight are unchanged by hypothetical reasoning.
        print(json.dumps(dict(result=v,goals=x["query"]["goals"],frontier=c["frontier"]),indent=2))
