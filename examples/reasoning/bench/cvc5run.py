#!/usr/bin/env python3
"""Run cvc5 (Python API) on an SMT-LIB 2 file; prints sat / unsat / unknown."""
import sys
import cvc5

tm = cvc5.TermManager()
s = cvc5.Solver(tm)
s.setOption("produce-models", "false")
s.setOption("full-saturate-quant", "true")  # complete instantiation for refutations (EPR)
if len(sys.argv) > 2:
    s.setOption("tlimit-per", str(int(float(sys.argv[2]) * 1000)))  # per query, so an incremental script gets the limit per answer
p = cvc5.InputParser(s)
p.setFileInput(cvc5.InputLanguage.SMT_LIB_2_6, sys.argv[1])
sm = p.getSymbolManager()
while True:
    cmd = p.nextCommand()
    if cmd.isNull():
        break
    out = cmd.invoke(s, sm)
    if out.strip():
        print(out.strip(), flush=True)
