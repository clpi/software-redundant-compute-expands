"""Emit and check a Lean certificate that H is a minimal explanation of observations O on the
whole log, through `Canon.Abduction.certificate` (cone check over every record, minimalB over
the cone). The Lean kernel evaluates both checks by `decide`; nothing here is trusted.

Usage: certify.py RESULT.json OUTDIR NAME 'h1,h2,...' 'o1,o2,...'   (term names)
Prints one JSON line: {name, ok, seconds, cone_records, records, file_sha256, axioms}.
"""
import hashlib, json, os, subprocess, sys, time

res = json.load(open(sys.argv[1]))
outdir, name = sys.argv[2], sys.argv[3]
names = res["names"]; ids = {n: i for i, n in enumerate(names)}
H = [ids[x] for x in sys.argv[4].split(",") if x]
O = [ids[x] for x in sys.argv[5].split(",") if x]
recs = res["recs"]; A = res["A"]

# backward cone of O and bot
byhead = {}
for r in recs:
    byhead.setdefault(r["head"], []).append(r)
T, st = set(), list(O) + [0]
while st:
    x = st.pop()
    if x in T:
        continue
    T.add(x)
    for r in byhead.get(x, ()):
        st.extend(r["premises"])
T = sorted(T)
Tset = set(T)


def lst(xs):
    return "[" + ", ".join(str(x) for x in xs) + "]"


cone = [r for r in recs if r["head"] in Tset]


def clos_order(roots):
    """Closure of the cone records from roots, in firing order."""
    S, order, ch = set(roots), list(dict.fromkeys(roots)), True
    while ch:
        ch = False
        for r in cone:
            if r["head"] not in S and all(p in S for p in r["premises"]):
                S.add(r["head"]); order.append(r["head"]); ch = True
    return S, order


EXPECT_FAIL = "--expect-fail" in sys.argv  # planted false hypothesis: the kernel must refuse it
Sall, tr = clos_order(H)
assert EXPECT_FAIL or (all(o in Sall for o in O) and 0 not in Sall), "not an explanation"
Sx = []
for x in H:
    Sx_, _ = clos_order([y for y in H if y != x])
    assert EXPECT_FAIL or not all(o in Sx_ for o in O), f"not minimal: {x}"
    Sx.append((x, sorted(Sx_)))

lines = [
    "import Abduction", "", "set_option maxRecDepth 100000", "", "namespace Canon", "namespace AbductionCert", "open Abduction", "",
    "def idc : Chain := ⟨fun _ c => c, 0, 0, Nat.le_refl 0⟩", "",
    "def L : List Rec := [",
    ",\n".join(f"  ⟨{r['id']}, 0, [], {lst(r['premises'])}, {r['head']}⟩" for r in recs),
    "]", "",
    "def Lc : List Rec := [",
    ",\n".join(f"  ⟨{r['id']}, 0, [], {lst(r['premises'])}, {r['head']}⟩" for r in recs if r["head"] in Tset),
    "]", "",
    f"def P : Problem := ⟨idc, L, 0, fun _ => true, 0, {lst(sorted(H))}, {lst(O)}⟩",
    f"def T : List Nat := {lst(T)}",
    f"def H : List Nat := {lst(H)}", "",
    "theorem cone_ok : coneClosedB P.ch P.L P.r P.q T = true := by decide +kernel",
    "theorem cone_eq : coneOf P.ch P.L P.r T = Lc := by decide +kernel",
    "theorem obs_ok : P.O.all (fun o => decide (o ∈ T)) = true := by decide +kernel",
    "theorem bot_ok : decide (P.bot ∈ T) = true := by decide +kernel",
    f"def tr : List Nat := {lst(tr)}",
    f"def Sbot : List Nat := {lst(sorted(Sall))}",
    "def Sx : List (Nat × List Nat) := [" + ", ".join(f"({x}, {lst(S_)})" for x, S_ in Sx) + "]", "",
    "theorem min_ok : certB { P with L := Lc } H tr Sbot Sx = true := by decide +kernel", "",
    f"/-- {name}: H is a duplicate-free minimal explanation of O on the whole log. -/",
    "theorem minimal_explanation : H.Nodup ∧ Minimal P H :=",
    "  certificate_fast P T H Lc tr Sbot Sx cone_ok cone_eq obs_ok bot_ok min_ok", "",
    "end AbductionCert", "end Canon", "",
    "#print axioms Canon.AbductionCert.minimal_explanation", "",
]
os.makedirs(outdir, exist_ok=True)
path = os.path.join(outdir, f"{name}.lean")
open(path, "w").write("\n".join(lines))
proof = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "proof")
env = dict(os.environ, LEAN_PATH=os.path.abspath(proof))
t = time.time()
p = subprocess.run([os.environ.get("LEAN", "lean"), "-DwarningAsError=true", path], capture_output=True, text=True, env=env)
secs = round(time.time() - t, 2)
out = p.stdout + p.stderr
ax = [l for l in out.splitlines() if "axioms" in l]
okax = all(a in ("propext", "Classical.choice", "Quot.sound") for l in ax
           for a in (l.split("[")[1].rstrip("]").replace(" ", "").split(",") if "[" in l else []))
ok = p.returncode == 0 and "error" not in out and len(ax) == 1 and okax
if EXPECT_FAIL:
    ok = p.returncode != 0 and "decide" in out  # refused by the kernel's evaluation
open(os.path.join(outdir, f"{name}.out"), "w").write(out)
print(json.dumps({"name": name, "ok": ok, "expect_fail": EXPECT_FAIL, "hyp": sys.argv[4].split(","), "obs": sys.argv[5].split(","), "result": os.path.basename(sys.argv[1]), "seconds": secs, "cone_terms": len(T),
                  "cone_records": sum(1 for r in recs if r["head"] in Tset), "records": len(recs),
                  "file_sha256": hashlib.sha256(open(path, "rb").read()).hexdigest(),
                  "axioms": ax[0] if ax else out[-300:]}))
sys.exit(0 if ok else 1)
