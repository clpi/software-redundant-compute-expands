#!/bin/sh
# Rerun the same-contract measurement. Needs Lean 4.19.0 (lean, leanc on PATH).
# Optional: IDOL_LIB=<clpi/idol-lib checkout> regenerates V2Data.lean first.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
B="$(mktemp -d)"
trap 'rm -rf "$B"' EXIT HUP INT TERM
if [ -n "${IDOL_LIB:-}" ]; then python3 "$HERE/gen_v2.py" "$IDOL_LIB" "$HERE/V2Data.lean"; fi
cp "$HERE/../../proof/Canon.lean" "$HERE/../../proof/Closure.lean" "$HERE/../../proof/Worklist.lean" "$B/"
cp "$HERE/EstateData.lean" "$HERE/V2Data.lean" "$HERE/Measure.lean" "$B/"
cd "$B"
export LEAN_PATH=.
for f in Canon Closure Worklist EstateData V2Data Measure; do
  lean -o "$f.olean" -c "$f.c" "$f.lean" > /dev/null
done
leanc -O3 -o measure Canon.c Closure.c Worklist.c EstateData.c V2Data.c Measure.c
./measure | tee "$HERE/run.txt"
grep '^JSON ' "$HERE/run.txt" | sed 's/^JSON //' > "$HERE/results.jsonl"
sha256sum "$HERE/EstateData.lean" "$HERE/V2Data.lean" "$HERE/results.jsonl"
