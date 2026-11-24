#!/bin/sh
# Equivalence-generalization gate: compiles the Lean file with
# warnings as errors and checks its axioms (when LEAN is set or lean
# is on PATH), reruns the corpus twice and checks determinism, then
# runs the fix gates.
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"
PROOF="${PROOF:-$HERE/../../proof/Generalize.lean}"
LEAN="${LEAN:-$(command -v lean || true)}"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

if [ -n "$LEAN" ] && [ -f "$PROOF" ]; then
  "$LEAN" -DwarningAsError=true "$PROOF" > "$TMP/lean.log" 2>&1
  if grep -Eq 'error|warning|sorryAx' "$TMP/lean.log"; then cat "$TMP/lean.log"; exit 1; fi
  BAD="$(sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' "$TMP/lean.log" | tr ',' '\n' | sed 's/ //g' | grep -Ev '^(propext|Classical.choice|Quot.sound)$' || true)"
  if [ -n "$BAD" ]; then echo "axiom outside allowed set: $BAD"; exit 1; fi
  echo "lean: $(grep -c 'axioms' "$TMP/lean.log") theorems checked, standard axioms only"
else
  echo "lean: skipped (set LEAN to check proof/Generalize.lean)"
fi

cd "$HERE"
python3 measure.py "$TMP/a.json" > /dev/null
python3 measure.py "$TMP/b.json" > /dev/null
cmp -s "$TMP/a.json" "$TMP/b.json" || { echo "measurement not deterministic"; exit 1; }
echo "results sha256: $(sha256sum "$TMP/a.json" | cut -c1-16)"
python3 gate.py "$TMP/a.json"
