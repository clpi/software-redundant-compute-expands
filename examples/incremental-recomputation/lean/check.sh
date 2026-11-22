#!/bin/sh
# Cold gate for the cone rules.
#   LEAN=/path/to/lean sh check.sh                  Cone.lean only (9 theorems)
#   LEAN=/path/to/lean sh check.sh <hma proof dir> [<HmaJoin dir>]
#                                                    also HmaJoin.lean over Hma.lean (9 more)
# HmaJoin.lean and AuditHma.lean live in the HMA repo at solver/incremental/lean;
# they are taken from here if present, else from the second argument, else from
# <hma proof dir>/../solver/incremental/lean.
# Warnings are errors; escape tokens are rejected; every printed axiom set must lie
# within {propext, Classical.choice, Quot.sound}; the printout count must match.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
hma=${1:-}
hj=${2:-}
LEAN=${LEAN:-lean}
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
export LEAN_PATH="$T"
"$LEAN" --version
units=""; want=0
[ -f "$here/Cone.lean" ] && { units="Cone AuditCone"; want=9; }
if [ -n "$hma" ]; then
  (cd "$hma" && "$LEAN" -DwarningAsError=true -o "$T/Hma.olean" Hma.lean > "$T/hma.out" 2>&1) || { cat "$T/hma.out"; echo "REJECT Hma build"; exit 1; }
  echo "Hma.lean sha256 $(sha256sum "$hma/Hma.lean" | cut -c1-16) (built unchanged)"
  units="$units HmaJoin AuditHma"; want=$((want + 9))
  if [ -z "$hj" ]; then
    if [ -f "$here/HmaJoin.lean" ]; then hj=$here; else hj="$hma/../solver/incremental/lean"; fi
  fi
  hj=$(cd "$hj" && pwd)
  for f in HmaJoin AuditHma; do [ -f "$hj/$f.lean" ] || { echo "REJECT $f.lean not found in $hj"; exit 1; }; done
fi
dir_of() { case $1 in HmaJoin|AuditHma) echo "$hj" ;; *) echo "$here" ;; esac; }
for f in $units; do
  d=$(dir_of "$f")
  case $f in Audit*) ;; *)
    if grep -En '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide|implemented_by|extern|unsafe|opaque|partial)([^[:alnum:]_]|$)' "$d/$f.lean"; then
      echo "REJECT escape token in $f.lean"; exit 1; fi ;;
  esac
  (cd "$d" && "$LEAN" -DwarningAsError=true -o "$T/$f.olean" "$f.lean" > "$T/$f.out" 2>&1) || { cat "$T/$f.out"; echo "REJECT $f"; exit 1; }
  echo "$f.lean sha256 $(sha256sum "$d/$f.lean" | cut -c1-16) built"
done
cat "$T"/Audit*.out > "$T/audit"
cat "$T/audit"
n=$(grep -c "depends on axioms\|does not depend on any axioms" "$T/audit")
[ "$n" -eq "$want" ] || { echo "REJECT expected $want printouts, got $n"; exit 1; }
bad=$(sed -n 's/.*depends on axioms: \[\([^]]*\)\].*/\1/p' "$T/audit" | tr ',' '\n' | sed 's/^ *//;s/ *$//' | sort -u | grep -vxE 'propext|Classical.choice|Quot.sound' || true)
[ -z "$bad" ] || { echo "REJECT axioms: $bad"; exit 1; }
echo "LEAN GATE: PASS ($want theorems, axioms within propext, Classical.choice, Quot.sound)"
