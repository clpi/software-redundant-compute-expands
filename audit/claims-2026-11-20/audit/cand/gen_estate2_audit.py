# Measurement scaffolding (Python), round 2. Builds the estate log as canonical records and
# writes EstateData.lean. Reads checkouts read-only; never runs any library or tool.
# Inputs: proof_estate.json, idol-lib checkout, idol-eyes checkout, idol-eyes browser-face
# files in the project folder (page.id, certify.id; sibling's local branch, not on main).
import json, re, sys, glob, os
proof, IL, IE, BF, out = sys.argv[1:6]
POSSIBLE, OBSERVED, QUALIFIED, DISQ, DEMANDED, PROPOSAL = 1, 2, 3, 4, 5, 7
terms, recs = {}, []
def t(name):
    if name not in terms: terms[name] = len(terms)
    return terms[name]
def rec(level, colors, prem, head, src):
    recs.append((len(recs), level, colors, [t(p) for p in prem], t(head), src))
stats = {}
# 1. proof estate (kernel-checked constants)
for c in json.load(open(proof)):
    rec(0, [OBSERVED, QUALIFIED], ["lean:" + d for d in c["deps"]], "lean:" + c["name"], "proof:" + c["module"])
# 2. idol-lib graphs (version 2 source projection)
def short(n): return f'il:{n["library"]}:{n["name"]}:{n["source"]["path"].split("/")[-1]}:{n["source"]["span"]["start_line"]}'
uniq = amb = 0; ndefs = 0
for f in sorted(glob.glob(os.path.join(IL, "graphs/*/graph.json"))):
    g = json.load(open(f))
    defs = {n["id"]: n for n in g["nodes"] if n["kind"] == "definition"}
    if os.environ.get("TOPLEVEL_ONLY"):
        def _top(n):
            p = os.path.join(IL, n["source"]["path"]); l = n["source"]["span"]["start_line"]
            line = open(p, errors="replace").read().split("\n")[l - 1]
            return line[:1] not in (" ", "\t")
        defs = {k: v for k, v in defs.items() if _top(v)}
    for nid, n in defs.items():
        d = short(n); ndefs += 1
        rec(0, [POSSIBLE], [], d, "idol-lib:source")
        prem = [d, "obs:" + d]
        for r in n.get("references", []):
            cs = [c for c in r["candidates"] if c in defs and c != nid]
            if not cs: continue
            if len(cs) == 1: prem.append("qual:" + short(defs[cs[0]])); uniq += 1
            else: prem.append(f'ref:{d}:{r["spelling"]}'); amb += 1
        # rule R1 (premise): qualified iff observed, every unique callee qualified, every reference resolved
        rec(0, [POSSIBLE], list(dict.fromkeys(prem)), "qual:" + d, "idol-lib:rule-R1")
        # demand D1 (premise): every definition qualified
        rec(0, [DEMANDED], [], "qual:" + d, "demand:D1")
stats["idol-lib"] = dict(defs=ndefs, unique_refs=uniq, ambiguous_refs=amb)
# 3. idol-eyes protocol modules + browser face
DEF = re.compile(r"^([A-Za-z][A-Za-z0-9]*)\s*:[^=\n]*=")
TOK = re.compile(r"[A-Za-z][A-Za-z0-9]*")
files = sorted(glob.glob(os.path.join(IE, "protocol/*.id"))) + [os.path.join(BF, "page.id"), os.path.join(BF, "certify.id")]
mods = {}
for p in files:
    m = os.path.basename(p)[:-3]; body = {}; cur = None
    for ln in open(p, errors="replace").read().splitlines():
        if ln.lstrip().startswith("#"): continue
        mm = DEF.match(ln)
        if mm: cur = mm.group(1); body.setdefault(cur, [])
        if cur is not None: body[cur].append(re.sub(r'"([^"\\]|\\.)*"', '""', ln.split(" #")[0]))
    mods[m] = body
where = {}
for m, b in mods.items():
    for nm in b: where.setdefault(nm, []).append(m)
eu = ea = 0
for m, b in mods.items():
    for nm, lines in b.items():
        d = f"ie:{m}:{nm}"
        rec(0, [POSSIBLE], [], d, "idol-eyes:source")
    for nm, lines in b.items():
        d = f"ie:{m}:{nm}"
        toks = set(TOK.findall("\n".join(lines))) - {nm}
        prem = [d]
        for tk in sorted(toks):
            if tk in b: prem.append(f"ie:{m}:{tk}"); eu += 1          # same module: definite
            # each protocol file is one standalone program: no cross-module references
        rec(0, [POSSIBLE], prem, f"ie:closed:{m}:{nm}", "idol-eyes:refs")
    # module capability: every definition closed, plus qualifying evidence
    rec(0, [POSSIBLE], [f"ie:closed:{m}:{nm}" for nm in b] + [f"evidence:{m}"], f"cap:{m}", "idol-eyes:module")
stats["idol-eyes"] = dict(modules=len(mods), defs=sum(len(b) for b in mods.values()), definite_refs=eu, ambiguous_refs=ea)
# measured evidence: browser campaign 1 admitted page.id on the five script-free tasks (decisions.txt)
rec(0, [OBSERVED, QUALIFIED], [], "evidence:page", "measured:campaign-1")
# browser face: script-free (page) plus a script engine (spa refused, 0/10 measured)
rec(0, [POSSIBLE], ["cap:page", "cap:script-engine"], "cap:browser", "idol-eyes:browser")
rec(0, [DEMANDED], [], "cap:script-engine", "demand:measured-gap")
# Chris's scope: idol-eyes is a general semantic intent -> action -> computer-use orchestrator.
# Premises: the repo's own modules and its own named open gaps (README, docs/harness.md, runtime.md, plans.md, reconciliation.md, acceptance.md).
named = ["solve-loop", "graph-authority", "outcome-publication", "cross-platform", "native-ui",
         "durable-recovery", "accessibility-discovery", "competitive-measurement", "mesh-integration"]
modcaps = [f"cap:{m}" for m in mods if m not in ("page", "certify")]
rec(0, [POSSIBLE], modcaps + ["cap:browser"] + [f"cap:{x}" for x in named], "eyes:orchestrator", "scope:chris")
rec(0, [POSSIBLE], ["cap:certify", "evidence:competitive-desktop"], "cap:competitive-measurement", "idol-eyes:acceptance")
rec(0, [DEMANDED], [], "eyes:orchestrator", "demand:chris")
for x in named:
    if x != "competitive-measurement": rec(0, [DEMANDED], [], f"cap:{x}", "demand:repo-named-gap")
# 4. ledger gaps with no recorded structure
for g in ["gap:S-02 provenance derivation", "gap:G2 yield cap in Lean", "gap:G4 implications 2-4"]:
    rec(0, [DEMANDED], [], g, "demand:ledger")
inv = sorted(terms, key=terms.get)
L = ["import Canon", "/-! Generated by scaffold/gen_estate2.py. Do not edit. -/", "namespace Estate", "open Canon", "",
     "def names : Array String := #[" + ", ".join(json.dumps(n) for n in inv) + "]", "",
     "def srcs : Array String := #[" + ", ".join(json.dumps(r[5]) for r in recs) + "]", "",
     "def log : List Rec := ["]
L += ["  ⟨%d, %d, %s, %s, %d⟩," % (i, lv, json.dumps(cs), json.dumps(ps), h) for i, lv, cs, ps, h, _ in recs]
L[-1] = L[-1].rstrip(",")
L += ["]", "", "end Estate", ""]
open(out, "w").write("\n".join(L))
stats["records"] = len(recs); stats["terms"] = len(terms)
print(json.dumps(stats))
