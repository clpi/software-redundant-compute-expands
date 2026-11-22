#!/bin/sh
# Rerun the monotone synthesis proofs, controls, mutants and the loop on real data.
#   OPT  checkout of clpi/software-optimality at 3418711 (draft PR 19, ClosureStrength)
#   IL   checkout of clpi/idol-lib containing 0be14af and f754884
#   IQ   the idol-qualification receipts directory (graphs, resolve, receipts; hashes below)
#   LEAN lean 4.19.0
set -eu
cd "$(dirname "$0")"
LEAN="${LEAN:-lean}"
: "${OPT:?checkout of clpi/software-optimality at 3418711}"
: "${IL:?checkout of clpi/idol-lib}"
: "${IQ:?idol-qualification receipts directory}"
OUT="${OUT:-receipts}"
mkdir -p "$OUT"
tmp=$(mktemp -d); trap 'rm -rf "$tmp"' EXIT HUP INT TERM

got=$(git -C "$OPT" rev-parse HEAD)
case "$got" in 3418711*) echo "pin ok software-optimality $got";; *) echo "WRONG PIN software-optimality $got"; exit 1;; esac
(cd "$OPT" && sha256sum -c - <<EOF
a96ebcd998e1cd3703b9cc1fb6b3f2d73f6df8610bd0b34b3199afbb78f42f65  Qualification.lean
fe533a245b11156be673649c880e12f2e9edb623534d7757f4ff6673f2b6796f  ExecutableClosure.lean
9f24a2dc4248f1cb86f2fdc9d9b7af5f5f55b5aa9f2c73a9d95b30eee5f232bd  ClosureStrength.lean
EOF
)
git -C "$IL" cat-file -e 0be14af8d63a749c5121dbf790665cf38593b077 && git -C "$IL" cat-file -e f754884
"$LEAN" --version

echo "== Lean"
if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|partial)([^[:alnum:]_]|$)' MonotoneSynthesis.lean MonotoneSynthesisControls.lean; then
  echo "escape found"; exit 1; fi
mkdir -p "$tmp/opt"
for f in Qualification ExecutableClosure ClosureStrength; do
  cp "$OPT/$f.lean" "$tmp/opt/"
  (cd "$tmp/opt" && LEAN_PATH=. "$LEAN" -DwarningAsError=true -o "$f.olean" "$f.lean" > /dev/null)
done
cp MonotoneSynthesis.lean MonotoneSynthesisControls.lean "$tmp/"
LOG="$OUT/lean.txt"; : > "$LOG"
for f in MonotoneSynthesis MonotoneSynthesisControls; do
  (cd "$tmp" && LEAN_PATH="$tmp/opt:$tmp" "$LEAN" -DwarningAsError=true -o "$f.olean" "$f.lean") >> "$LOG" 2>&1 || { cat "$LOG"; exit 1; }
done
if grep -Eq 'sorryAx|error:|warning:' "$LOG"; then cat "$LOG"; exit 1; fi
n=$(grep -c 'depends on axioms\|does not depend on any axioms' "$LOG")
bad=$(sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' "$LOG" | tr ',' '\n' | sed 's/^ *//; s/ *$//' | sort -u | grep -vxE 'propext|Classical.choice|Quot.sound' || true)
[ -z "$bad" ] || { echo "axiom outside allowed set: $bad"; exit 1; }
echo "PASS Lean: $n theorems printed, axioms within propext, Classical.choice, Quot.sound" | tee -a "$LOG"

echo "== Lean mutants (each must fail to compile)"
mutant() { name=$1; file=$2; from=$3; to=$4
  rm -rf "$tmp/m"; mkdir "$tmp/m"; cp "$tmp"/Monotone*.lean "$tmp/m/"
  python3 -I -c "import sys;s=open(sys.argv[1]).read();assert sys.argv[2] in s, sys.argv[2];open(sys.argv[1],'w').write(s.replace(sys.argv[2],sys.argv[3],1))" "$tmp/m/$file" "$from" "$to"
  ok=1
  for f in MonotoneSynthesis MonotoneSynthesisControls; do
    (cd "$tmp/m" && LEAN_PATH="$tmp/opt:$tmp/m" "$LEAN" -DwarningAsError=true -o "$f.olean" "$f.lean" > "$tmp/m/out" 2>&1) || ok=0
  done
  if [ $ok -eq 1 ]; then echo "MUTANT SURVIVED $name"; exit 1; else echo "mutant killed $name" | tee -a "$LOG"; fi; }
mutant drop-coverage MonotoneSynthesis.lean '      (∀ a, reach P L a → reach P (L ++ [.retire i n]) a) →
      Admit P V L (.retire i n)' '      Admit P V L (.retire i n)'
mutant drop-premise-check MonotoneSynthesis.lean '      (∀ p, p ∈ x.prem → reach P L p) →
      Admit P V L (.add x)' '      Admit P V L (.add x)'
mutant drop-verifier MonotoneSynthesis.lean '  | add {x : Art A} :
      V x →' '  | add {x : Art A} :'
mutant drop-never-retired MonotoneSynthesis.lean '      (∀ n, Entry.retire x.id n ∉ L) →
      (∀ p, p ∈ x.prem → reach P L p) →' '      (∀ p, p ∈ x.prem → reach P L p) →'
mutant replace-any-head MonotoneSynthesis.lean ' && decide (z.head = y.head) &&' ' &&'
mutant unsaturated-exact MonotoneSynthesis.lean '(hfrom : From C L) (hsat : Saturated P V C L) (a : A) :' '(hfrom : From C L) (hsat : True) (a : A) :'
mutant abstraction-underived MonotoneSynthesis.lean '(hderiv : Derives (fun b => P b ∨ b ∈ x.prem) (rules L) x.head)' '(hderiv : True)'
mutant single-pass-saturated MonotoneSynthesisControls.lean '¬ Saturated P0 V0 C [.add x0] ∧' 'Saturated P0 V0 C [.add x0] ∧'
mutant retire-uncovered-ok MonotoneSynthesisControls.lean '∧ ¬ Admit P0 V0 L (.retire 0 2)' '∧ Admit P0 V0 L (.retire 0 2)'

echo "== loop on real data"
python3 -I gen_idol.py "$IQ" "$IL" > "$OUT/stream.jsonl"
sha256sum "$OUT/stream.jsonl"
gs=0; python3 -I gate.py "$OUT/stream.jsonl" loop.py > "$OUT/gate.txt" || gs=$?
cat "$OUT/gate.txt"
[ "$gs" -eq 0 ] || { echo "GATE FAILED (exit $gs)"; exit 1; }
for o in history reverse shuffle:1 shuffle:2 shuffle:3; do
  python3 -I loop.py "$OUT/stream.jsonl" --order "$o" --abstractions
done > "$OUT/summaries.jsonl"
python3 -I loop.py "$OUT/stream.jsonl" --strict > "$OUT/summary-strict.json"
python3 -I loop.py "$OUT/stream.jsonl" --raw > "$OUT/summary-raw.json"
python3 -I loop.py "$OUT/stream.jsonl" --trace > "$OUT/trace-history.jsonl"
python3 -I loop.py "$OUT/stream.jsonl" --emit-events "$OUT/events.jsonl" > /dev/null
rm -f "$tmp/state.json"
for b in $(python3 -I -c "import json,sys;print('\\n'.join(dict.fromkeys(json.loads(l)['batch'] for l in open(sys.argv[1]))))" "$OUT/events.jsonl"); do
  python3 -I ingest.py "$tmp/state.json" "$OUT/events.jsonl" --batch "$b"
done > "$OUT/ingest.jsonl"
python3 -I ingest.py "$tmp/state.json" --summary >> "$OUT/ingest.jsonl"
echo "ALL PASS"
