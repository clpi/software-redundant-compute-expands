#!/bin/sh
# elimination order: rung 1 runs the kernel on appends as they land; this script only builds the kernel,
# feeds it the control logs, the mutants and the replay logs, and prints what it said.
# usage: run.sh <idol binary> <idol-lib checkout with sha256/sha256.id> <out dir>
#   expects in <out dir>: ctl/ (controls.py), eyes/c<N>-a<0|1>/ (replay_eyes.py), root/ and space.tsv
#   (replay_space.py; root as /mnt/project-files/rung0/receipts/README-root.txt describes, with
#   root/controls -> rung0/receipts/control-inputs), and optionally rung0/ -> rung0/receipts/controls.
set -e
idol=$1; lib=$2; out=$3
here=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
build() {  # build <kernel source> <binary>
  cat "$lib/sha256/sha256.id" "$1" > "$work/unit.id"
  "$idol" check "$work/unit.id" >/dev/null
  "$idol" dump-c "$work/unit.id" > "$work/unit.c"
  cc -O2 -o "$2" "$work/unit.c" -lm 2>/dev/null
}
build "$here/kernel.id" "$work/kernel"
echo "kernel.id sha256 $(sha256sum "$here/kernel.id" | cut -c1-64)"
echo "idol sha256 $(sha256sum "$idol" | cut -c1-64)"
judge() {  # judge <kernel binary> <control name> : PASS when the kernel says what expect.json says
  printf '%s\n%s' "$out/ctl/$2.tsv" "$out/ctl" | "$1" > "$work/o.txt"
  python3 -I - "$out/ctl/expect.json" "$2" "$work/o.txt" <<'EOF'
import json, sys
e = json.load(open(sys.argv[1]))[sys.argv[2]]
lines = open(sys.argv[3]).read().splitlines()
verdicts = [l for l in lines if l.startswith("ACCEPT") or l.startswith("REFUSE")]
last = verdicts[-1] if verdicts else ""
prefix_ok = len(verdicts) == e["records"] and all(v.startswith("ACCEPT") for v in verdicts[:-1])
reason = last.split(": ", 1)[1] if ": " in last else ""
names = [x.strip().split(" ")[0].rstrip(":") for x in reason.split("; ") if x.strip()]
if e["refused_check"] is None:
    ok = prefix_ok and last.startswith("ACCEPT")
else:
    ok = prefix_ok and last.startswith("REFUSE") and names == [e["refused_check"]]
print(("PASS " if ok else "MISS ") + sys.argv[2] + " | " + last[:150])
EOF
}
echo "== controls"
for f in "$out"/ctl/*.tsv; do judge "$work/kernel" "$(basename "$f" .tsv)"; done
echo "== mutants: each removes one check; the named controls must now fail"
for m in contractOnce buildAfterContract buildLeak runRegistered runHarness runSubject revealSeal factGrounded \
         heldout cover correct peak margin merged nullBase; do
  python3 -I "$here/mutate.py" "$here/kernel.id" "$work/m.id" "$m"
  build "$work/m.id" "$work/mk"
  flipped=""
  for f in "$out"/ctl/*.tsv; do
    c=$(basename "$f" .tsv)
    case "$(judge "$work/mk" "$c")" in MISS*) flipped="$flipped $c";; esac
  done
  echo "mutant no-$m: controls that now fail:${flipped:- none}"
done
echo "== replay: idol-eyes campaigns (a0 = the campaign's own dimensions, a1 = plus the audit's)"
for d in "$out"/eyes/*/; do
  printf '%s\n%s' "$d/log.tsv" "$d" | "$work/kernel" > "$d/kernel.out"
  python3 -I - "$d" <<'EOF'
import json, sys
d = sys.argv[1]
m = json.load(open(d + "/map.json"))
out = open(d + "/kernel.out").read().splitlines()
ref = [l for l in out if l.startswith("REFUSE")]
print(d.rstrip("/").split("/")[-1], "| records refused:", len(ref), "|", out[-1])
for line, s in sorted(m["claims"].items(), key=lambda x: int(x[0])):
    v = [l for l in out if l.startswith("ACCEPT line " + line + " ") or l.startswith("REFUSE line " + line + " ")]
    print("   claim", s, ":", v[0].split(": ", 1)[-1] if v else "no verdict")
nonclaim = sorted({l.split(": ", 1)[1].split(":")[0][:60] for l in ref if " beats:" not in l})
if nonclaim:
    print("   other refusals:", nonclaim)
EOF
done
echo "== replay: level 3 receipts and space data theorems (rung 0 log plus derivations)"
start=$(date +%s.%N)
printf '%s\n%s' "$out/space.tsv" "$out/root" | "$work/kernel" > "$out/space.out"
end=$(date +%s.%N)
echo "seconds $(echo "$end - $start" | bc)"
tail -2 "$out/space.out"
grep -E '^(ACCEPT|REFUSE) line [0-9]+ (derive|fact|work)' "$out/space.out" || true
python3 -I - "$out/space.out" <<'EOF'
import collections, re, sys
c = collections.Counter()
for l in open(sys.argv[1]):
    if l.startswith("REFUSE") and " claim: " in l:
        why = l.rstrip("\n").rsplit(": ", 1)[1]
        why = re.sub(r"line \d+ of \S+", "line N of F", why)
        why = re.sub(r"run:\S+", "run:H", why)
        c[why] += 1
for why, n in c.most_common():
    print("%6d qualification claims refused: %s" % (n, why))
EOF
if [ -d "$out/rung0" ]; then
  echo "== rung 0 controls on this kernel (expect.json from /mnt/project-files/rung0/receipts/controls)"
  for f in "$out"/rung0/*.tsv; do
    c=$(basename "$f" .tsv)
    printf '%s\n%s' "$f" "$out/root" | "$work/kernel" > "$work/r0.txt" 2>&1
    python3 -I - "$out/rung0/expect.json" "$c" "$work/r0.txt" <<'EOF'
import json, sys
e = json.load(open(sys.argv[1]))[sys.argv[2]]
out = open(sys.argv[3]).read()
last = out.strip().splitlines()[-1]
ok = e["outcome"] in last.replace(" accepted 0", "") and (e["reason"] is None or any(l.startswith("REFUSE") and e["reason"] in l for l in out.splitlines()))
print(("PASS " if ok else "MISS ") + sys.argv[2] + " | " + last)
EOF
  done
fi
