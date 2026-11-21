#!/bin/sh
# End to end: rebuild the whole semantic-axes log from the raw traces into
# a fresh directory, check every claim against it, and run the proof gate.
#   sh run_all.sh OUT IDOL_LIB        (REPEATS=5 is the contract; REPEATS=1 for a fast check)
# Deterministic claims (ops, correctness, undo, merge, visibility, front
# updates, validity) must reproduce exactly; wall-time-dependent ones are
# reported as skipped, since timings are re-measured.
set -e
OUT="$1"; IDOL_LIB="$2"
[ -n "$OUT" ] && [ -n "$IDOL_LIB" ] || { echo "usage: sh run_all.sh OUT IDOL_LIB"; exit 2; }
[ ! -e "$OUT/space.jsonl" ] || { echo "$OUT/space.jsonl exists; the log is append-only, use a fresh directory"; exit 2; }
cd "$(dirname "$0")"
python3 axes_run.py dev "$OUT"
python3 fix_joint.py "$OUT/space.jsonl" dev 1,2,3,4
python3 axes_select.py "$OUT/space.jsonl" dev > "$OUT/select.dev.json"
python3 axes_heldout.py "$OUT" "$IDOL_LIB"
python3 rescore.py "$OUT/space.jsonl"
python3 axes_select.py "$OUT/space.jsonl" dev > "$OUT/select2.dev.json"
python3 axes_select.py "$OUT/space.jsonl" heldout > "$OUT/select2.heldout.json"
python3 axisfront.py "$OUT/space.jsonl" dev
python3 axisfront.py "$OUT/space.jsonl" heldout
python3 round2.py "$OUT" dev
python3 axes_select.py "$OUT/space.jsonl" r2-dev > "$OUT/select.r2-dev.json"
python3 round2.py "$OUT" heldout "$IDOL_LIB"
python3 axes_select.py "$OUT/space.jsonl" r2-heldout > "$OUT/select.r2-heldout.json"
python3 axisfront.py "$OUT/space.jsonl" r2-dev
python3 axisfront.py "$OUT/space.jsonl" r2-heldout
python3 verify.py "$OUT/space.jsonl" --rerun
(cd ../../proof && sh check.sh)
