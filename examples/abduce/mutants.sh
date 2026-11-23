#!/bin/sh
# Each mutant weakens one check of proof/Abduce.lean; compiling Abduce.lean and
# AbduceControls.lean must then fail. Prints one line per mutant; exit 1 if any survives.
set -eu
here=$(cd "$(dirname "$0")" && pwd)
LEAN="${LEAN:-lean}"
w=$(mktemp -d); trap 'rm -rf "$w"' EXIT
cp "$here/../../proof/Canon.lean" "$here/../../proof/Closure.lean" "$here/../../proof/AbduceControls.lean" "$w/"
(cd "$w" && LEAN_PATH=. "$LEAN" -o Canon.olean Canon.lean >/dev/null && LEAN_PATH=. "$LEAN" -o Closure.olean Closure.lean >/dev/null)
survived=0
mut() {  # mut <name> <python replace: old> <new>
  python3 - "$here/../../proof/Abduce.lean" "$w/Abduce.lean" "$2" "$3" <<'EOF'
import sys
s = open(sys.argv[1]).read()
assert s.count(sys.argv[3]) >= 1, "mutation site missing: " + sys.argv[3]
open(sys.argv[2], "w").write(s.replace(sys.argv[3], sys.argv[4], 1))
EOF
  if (cd "$w" && LEAN_PATH=. "$LEAN" -DwarningAsError=true -o Abduce.olean Abduce.lean >"$w/err" 2>&1 \
        && LEAN_PATH=. "$LEAN" -DwarningAsError=true AbduceControls.lean >"$w/err" 2>&1); then
    echo "SURVIVED $1"; survived=$((survived + 1))
  else
    first=$(grep -m1 'error' "$w/err" | sed 's/^[^:]*\///' | cut -c1-90)
    echo "killed $1 :: $first"
  fi
}
mut no-consistency '&& !decide (P.bot ∈ closWith P c H))' '&& true)'
mut no-abducible-check 'H.all (fun h => decide (h ∈ P.A)) &&
    (P.O.all' 'true &&
    (P.O.all'
mut no-erase-minimality '&& H.all (fun x => !explainsB P c (H.erase x))' '&& H.all (fun x => !explainsB P c (H.erase x) || true)'
mut no-nodup 'decide H.Nodup && explainsB P c H &&' 'explainsB P c H &&'
mut cone-unclosed '(proj ch r e).1.all (fun p => decide (p ∈ T)))' 'true)'
mut closed-skips-roots 'H.all (fun h => decide (h ∈ S)) &&
    L.all' 'H.all (fun _ => true) &&
    L.all'
mut trace-accepts-anything '(decide (a ∈ H) || L.any' '(true || L.any'
mut admit-ignores-verdict 'if verified && minimalB P c H then' 'if (verified || true) && minimalB P c H then'
mut dom-not-strict '&& (decide (b.cover < a.cover) || decide (a.cost < b.cost))' ''
mut cert-skips-bot '&& !decide (P.bot ∈ Sbot) &&' '&& !decide (P.bot ∈ ([] : List Nat)) &&'
echo "mutants survived: $survived"
[ "$survived" -eq 0 ]
