# elimination order: rung 1 appends controls as records on the log itself; this script only writes the
# same control logs as proof/AdmissionControls.lean in the kernel's TSV form. It decides nothing.
# usage: python3 -I controls.py <out dir>
import hashlib, json, os, sys

out = sys.argv[1]
os.makedirs(out + "/blobs", exist_ok=True)


def blob(name, text):
    p = "blobs/" + name
    with open(out + "/" + p, "w") as f:
        f.write(text)
    return p


def sha(p):
    return hashlib.sha256(open(out + "/" + p, "rb").read()).hexdigest()


HB = blob("harness.txt", "harness 9 9\n")
HB2 = blob("harness-other.txt", "harness 8 8 (start-up inside the timed scope)\n")
HO = blob("heldout.txt", "held-out 7 7 7\n")
HX = blob("heldout-swapped.txt", "held-out 6 6 6\n")
W10 = blob("work10.txt", "dev workload 5 5\n")


def trace(t):
    # Lean blob [ok, s1, s2, ...] as a trace file
    name = "t-" + "-".join(map(str, t)) + ".txt"
    return blob(name, ("ok" if t[0] == 1 else "fail") + "\n" + "".join("%d\n" % x for x in t[1:]))


def contract(reps=1, sealed=HO):
    return ["contract", "0", sha(HB), sha(sealed), "2", str(reps)]


def run(s, w, d, t, h=HB):
    return ["run", "7", str(s), str(w), str(d), h, trace(t)]


def cell(s, w, t1, t2):
    return [run(s, w, 1, t1), run(s, w, 2, t2)]


# Lean positions 0..22 are lines 1..23 here
pre = ([["dim", "0", "1"], ["dim", "0", "2"], ["work", "0", "10", W10], ["config", "0", "20"],
        ["config", "0", "21"], ["null", "0", "30"], contract(), ["build", "0", "40", "3"]]
       + cell(40, 10, [1, 3], [1, 4]) + cell(20, 10, [1, 50], [1, 60]) + cell(21, 10, [1, 10], [1, 12])
       + [run(30, 10, 1, [0, 0]), ["reveal", "7", "11", HO]]
       + cell(40, 11, [1, 3], [1, 4]) + cell(20, 11, [1, 50], [1, 60]) + cell(21, 11, [1, 10], [1, 12])
       + [run(30, 11, 1, [0, 0])])
assert len(pre) == 23


def setp(i, r):
    p = [list(x) for x in pre]
    p[i] = r
    return p


claim = ["beats", "0", "40"]
controls = {
    "p0-honest": (pre + [claim, ["derive", "0", "9,10"]], ["fact", "25"], None),
    "c01-goodhart": (pre + [["dim", "0", "3"], run(20, 10, 3, [1, 5]), run(20, 11, 3, [1, 5])], claim, "cover"),
    "c02-reselect": (pre, ["contract", "0", sha(HB), sha(HX), "2", "1"], "contractOnce"),
    "c03-tuned-after-reveal": (pre + [["build", "0", "41", "3"]] + cell(41, 10, [1, 3], [1, 4]) + cell(41, 11, [1, 3], [1, 4]),
                               ["beats", "0", "41"], "heldout"),
    "c04-seal-swap": (pre[:15], ["reveal", "7", "11", HX], "revealSeal"),
    "c05-harness-mismatch": (pre, run(21, 10, 1, [1, 100], HB2), "runHarness"),
    "c06-transcribed": (pre + [["derive", "0", "3"]], ["fact", "24"], "factGrounded"),
    "c07-name-match": (pre, run(99, 10, 1, [1, 1]), "runSubject"),
    "c08-fast-but-wrong": (setp(8, run(40, 10, 1, [0, 3])), claim, "correct"),
    "c09-do-nothing-passes": (setp(14, run(30, 10, 1, [1, 0])), claim, "nullBase"),
    "c10-inside-floor": (setp(12, run(21, 10, 1, [1, 4])), claim, "margin"),
    "c11-unmeasured-peak": (pre + [["dim", "0", "4"], run(40, 10, 4, [1, 1]), run(40, 11, 4, [1, 1])], claim, "peak"),
    "c12-answer-replay": (pre, ["build", "0", "42", "11"], "buildLeak"),
    "c13-weak-comparator": (setp(8, run(40, 10, 1, [1, 20])), claim, "margin"),
    "c14-no-heldout": (pre[:15], claim, "heldout"),
    "c15-lucky-run": (setp(6, contract(reps=3)), claim, "cover"),
    "c16-build-before-contract": (pre[:6], ["build", "0", "40", "3"], "buildAfterContract"),
    "c17-unregistered-run": (pre, run(40, 12, 1, [1, 1]), "runRegistered"),
}
expect = {}
for name, (prefix, last, check) in controls.items():
    rows = prefix + [last]
    with open(out + "/" + name + ".tsv", "w") as f:
        f.write("".join("\t".join(r) + "\n" for r in rows))
    expect[name] = {"records": len(rows), "refused_check": check}
json.dump(expect, open(out + "/expect.json", "w"), indent=1, sort_keys=True)
print(len(controls), "controls written")
