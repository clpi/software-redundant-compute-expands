# elimination order: rung 1 has gen.py append its derivation itself; this script appends to the rung 0
# replay log the derivations behind idol-lib space's data theorems and one fact per theorem family. It
# decides nothing: the kernel judges whether each fact's evidence is grounded in runs.
# usage: python3 -I replay_space.py <rung0 replay.tsv> <root> <out.tsv>
#
# Families (idol-lib space README claim table at master c3ecf26):
#  level3   Level3.idol_runs_pass, level3_counts, qualified_have_receipt: Data.lean's level 3 part is
#           gen.py over the Idol battery receipts, so the derivation's inputs are the receipt records.
#  level1   WitnessedV1 (qualified iff observed plus gate, substring observations): genv1.py over the
#           hypergraph branch's scanner output, whose inputs are source bytes, not runs. Encoded as a
#           derivation from the library file records.
#  lz4      Economics.lz4_measured_loss: timings typed in from port/lz4.md. Encoded as a workload-like
#           record holding that document's bytes; the theorem's data derives from it.
import sys

src, root, out = sys.argv[1], sys.argv[2], sys.argv[3]
rows = [l.rstrip("\n").split("\t") for l in open(src) if l.strip()]
receipts = [i + 1 for i, r in enumerate(rows) if r[0] == "receipt"]
files = [i + 1 for i, r in enumerate(rows) if r[0] == "file" and r[2].endswith(".id")
         and not r[2].endswith("vectors.id") and not r[2].endswith("battery.id")]
extra = []


def add(*r):
    extra.append(list(map(str, r)))
    return len(rows) + len(extra)


lz4 = add("work", "space", "lz4-md", "lib/port/lz4.md")
d3 = add("derive", "gen.py:level3", ",".join(map(str, receipts)))
d1 = add("derive", "genv1.py:level1", ",".join(map(str, files)))
dl = add("derive", "Economics.lz4", str(lz4))
f3 = add("fact", str(d3))
f1 = add("fact", str(d1))
fl = add("fact", str(dl))
with open(out, "w") as f:
    for r in rows + extra:
        f.write("\t".join(r) + "\n")
print("receipts", len(receipts), "library files", len(files), "facts at lines", {"level3": f3, "level1": f1, "lz4": fl})
