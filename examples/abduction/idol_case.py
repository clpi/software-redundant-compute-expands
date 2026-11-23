"""Replay the current and historical Idol continuation witnesses separately."""
import argparse
import json
from pathlib import Path
from subprocess import run
import sys
from tempfile import TemporaryDirectory
from abduction import Ledger,Query
from check_abduction import replay

def fixture(source, expect="either"):
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
    def active_payloads(state):
        return sorted(json.dumps({k:v for k,v in state["arts"][str(i)].items() if k!="id"},sort_keys=True) for i in state["live"])
    if ("arts" in warm and "arts" in cold and "live" in warm and "live" in cold
        and warm["reach"]==cold["reach"] and active_payloads(warm)==active_payloads(cold)
        and len(cold["reach"])==329
        and len(cold["live"])==330 and not warm.get("pending") and not cold.get("pending")):
        assert expect!="historical", "expected the pinned historical discrepancy"
        return dict(status="aligned", reachable=329, activePayloads=330,
                    missing=[], remedies=[], authority=False)
    assert expect!="repaired", "expected exact current continuation"
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
    ap.add_argument("--expect",choices=("either","historical","repaired"),default="either")
    a=ap.parse_args()
    x=fixture(a.example_dir.resolve(),a.expect)
    if x.get("status")=="aligned":
        if a.emit_input: ap.error("repaired continuation has no abduction input; use the historical pin")
        print(json.dumps(x,sort_keys=True))
        raise SystemExit(0)
    if a.emit_input:
        print(json.dumps(x,sort_keys=True))
    else:
        l=Ledger();l.append(x["records"])
        c=l.query(Query(**x["query"]),x["weights"])
        v=replay(x["records"],x["query"],c,x["weights"])
        assert v["supports"]==v["nondominated"]==2
        # The actual missing eight are unchanged by hypothetical reasoning.
        print(json.dumps(dict(result=v,goals=x["query"]["goals"],frontier=c["frontier"]),indent=2))
