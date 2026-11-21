# elimination order: rung 1 derives mutants from the kernel's own graph; this script switches one named
# check of kernel.id off by text (the line that tests it becomes `if false`) and writes the mutant.
# usage: python3 -I mutate.py <kernel.id> <out.id> <check>
import sys

src, dst, check = sys.argv[1:4]
lines = open(src).read().split("\n")
pat = {
    "contractOnce": 'if why == "" and con[f[2]] != nil',
    "buildAfterContract": 'if why == "" and con[f[2]] == nil',
    "buildLeak": 'if why == "" and con[f[2]] != nil and holds(car',
    "runRegistered": 'if why == "" and not (isdim[c.dom',
    "runHarness": 'if why == "" and sha(root .. "/" .. f[6]) != c.harness',
    "runSubject": 'if why == "" and subj[c.dom .. " " .. f[3]] != true',
    "revealSeal": 'if why == "" and sha(root .. "/" .. f[4]) != c.sealed',
    "factGrounded": 'if why == "" and not gr',
    "heldout": 'if not heldok',
    "cover": 'if not covok',
    "correct": 'if not corok',
    "peak": 'if not peakok',
    "margin": 'if not marok',
    "nullBase": 'if not nullok',
}
if check == "merged":
    hits = [i for i, l in enumerate(lines) if l.strip() == "ncfg = cs[0]"]
    assert len(hits) == 1, hits
    i = hits[0]
    lines[i] = lines[i].replace("ncfg = cs[0]", "ncfg = 1")
else:
    hits = [i for i, l in enumerate(lines) if l.strip().startswith(pat[check]) and (check != "contractOnce" or l.strip() == pat[check])]
    assert len(hits) == 1, (check, hits)
    i = hits[0]
    ind = len(lines[i]) - len(lines[i].lstrip())
    lines[i] = " " * ind + "if false"
open(dst, "w").write("\n".join(lines))
