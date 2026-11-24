#!/bin/sh
# Rerun every claim of the abduction apparatus. One script, in order:
#   1 family Lean gate (proof/check.sh, includes Abduce.lean and AbduceControls.lean)
#   2 Lean mutants of the abduction definitions (each must break a proof)
#   3 D0 planted causes on random logs (recovery, rejection, incremental = scratch = brute)
#   4 D1 monotone-synthesis pending artifacts, strict and raw, then Lean certificates
#   3b the same logs through #16 (examples/abduction) and its checker: explanation sets must agree
#   5 D2 gates: run, abduce (symptom causes and prerequisite actions read from the tree), test by
#     intervention / placebo / control, narrow prerequisites to a 1-minimal path set, planted faults
#   6 admission into the store (append only, monotone, verdicts re-decided) and its controls
#   7 SUMMARY.json and SHA256SUMS.txt
# Inputs:
#   LEAN    lean 4.19.0 on PATH or in $LEAN (lake next to it)
#   GATES   gate list (default gates-public.json: gates of this repository only)
#   BUNDLE  optional: the consolidated clpi/software-* bundle; when set, gates run in a clone of it
#           (the project's own gate list over the other theses is kept outside this public repo)
#   network access to github.com/clpi/software-optimality (public), and clpi/idol-lib (cloned by the resolver)
#   IQ_DIR  optional: the idol-qualification receipts directory is found by name under SEARCH
set -eu
here=$(cd "$(dirname "$0")" && pwd)
cd "$here"
LEAN="${LEAN:-lean}"
export PATH="$(dirname "$(command -v "$LEAN")"):$PATH"
GATES="${GATES:-gates-public.json}"
OUT="${OUT:-receipts}"
mkdir -p "$OUT"
WORK="${WORK:-$(mktemp -d)}"
export CACHE="$WORK/cache" MONO="$WORK/mono" RUNLOGS="$here/$OUT/runs"
echo "== 1 family gate"
sh ../../proof/check.sh > "$OUT/proof-check.txt" 2>&1 || { tail -20 "$OUT/proof-check.txt"; exit 1; }
tail -2 "$OUT/proof-check.txt"
echo "== 2 mutants"
./mutants.sh > "$OUT/mutants.txt" 2>&1 || { cat "$OUT/mutants.txt"; exit 1; }
tail -1 "$OUT/mutants.txt"
echo "== 3 planted"
python3 d_planted.py 200 "$OUT/d0-planted.json"
python3 crosscheck.py "$OUT/d0-planted.json" "$OUT/crosscheck.json"
echo "== 4 synthesis"
python3 d_synthesis.py ../monotone-synthesis/receipts/stream.jsonl strict 3 "$OUT/d1-strict.json" | head -2
python3 d_synthesis.py ../monotone-synthesis/receipts/stream.jsonl raw 3 "$OUT/d1-raw.json" | head -2
rm -rf "$OUT/certs"; mkdir -p "$OUT/certs"
JOBS="${JOBS:-2}" python3 certify_all.py "$OUT" "$OUT/certs" | tail -1
echo "== 5 gates"
if [ ! -d "$MONO" ]; then
  if [ -n "${BUNDLE:-}" ]; then git clone -q "$BUNDLE" "$MONO"
  else  # this repository's committed tree as the only thesis
    mkdir -p "$MONO/theses/redundant-compute-expands"
    git -C ../.. archive HEAD | tar -x -C "$MONO/theses/redundant-compute-expands"
    git -C "$MONO" init -q && git -C "$MONO" add -A && git -C "$MONO" -c user.email=a@b -c user.name=abduction commit -qm tree
  fi
fi
git clone -q https://github.com/clpi/software-optimality "$WORK/opt" && git -C "$WORK/opt" checkout -q 3418711
export ABD_OPT="$WORK/opt" ABD_IQ="${IQ_DIR:-/mnt/project-files/idol-qualification}"
[ -d /home/user/idol-lib/.git ] && export ABD_IL=/home/user/idol-lib || { git clone -q https://github.com/clpi/idol-lib "$WORK/il"; export ABD_IL="$WORK/il"; }
rm -rf "$RUNLOGS"; : > "$OUT/gates.jsonl"
python3 gates.py "$GATES" "$OUT/gates.jsonl"
echo "== 6 admission"
rm -f "$OUT/hypergraph.jsonl"
python3 admit.py "$OUT/hypergraph.jsonl" "$OUT" "$OUT/certs" "$OUT/gates.jsonl" "$RUNLOGS" > "$OUT/admit.json"
python3 admit_controls.py "$OUT" "$OUT/certs" "$OUT/gates.jsonl" "$RUNLOGS" > "$OUT/admit-controls.txt" || { cat "$OUT/admit-controls.txt"; exit 1; }
tail -1 "$OUT/admit-controls.txt"
echo "== 7 summary"
GATES_SPEC="$GATES" python3 summary.py "$OUT" > /dev/null
(cd "$OUT" && find . -type f ! -name SHA256SUMS.txt | LC_ALL=C sort | xargs sha256sum > SHA256SUMS.txt)
echo "ALL DONE: $OUT/SUMMARY.json"
