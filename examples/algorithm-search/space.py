# The one append-only hypergraph for the algorithm search.
#
# Every component, constraint, candidate, trace, objective,
# measurement, verdict and validation is a record of one log, in
# the shape of `Canon.Rec` (proof/Canon.lean): id, level, colors,
# premises, head. Terms and colors are interned strings. A record
# also carries a receipt (values, hashes, commands); the receipt is
# evidence, not identity. Records are appended, never edited; each
# line carries the sha256 of the previous line, so the log is
# tamper-evident and every reported number can be rebuilt from it
# alone (the H3 refutation test in claims-audit/CLAIMS.md).
#
# Views are projections of the log: a term is present at a color
# when some record with that color has it as head. Two records with
# the same head are two derivations of one term (total equivalence
# on the canonical key), so a candidate generated twice counts once.
import hashlib, json, os

class Space:
    def __init__(self, path):
        self.path = path
        self.recs = []
        self.terms, self.tname = {}, []
        self.colors, self.cname = {}, []
        self.prev = "0" * 64
        if os.path.exists(path):
            for line in open(path):
                o = json.loads(line)
                assert o["prev"] == self.prev, "broken chain at record %d" % o["id"]
                self.prev = hashlib.sha256(line.rstrip("\n").encode()).hexdigest()
                self._load(o)

    def term(self, s):
        if s not in self.terms:
            self.terms[s] = len(self.tname); self.tname.append(s)
        return self.terms[s]

    def color(self, s):
        if s not in self.colors:
            self.colors[s] = len(self.cname); self.cname.append(s)
        return self.colors[s]

    def _load(self, o):
        self.recs.append(o)

    def append(self, head, premises=(), colors=(), receipt=None, level=0):
        o = {"id": len(self.recs), "level": level,
             "colors": sorted(set(colors)), "premises": list(premises),
             "head": head, "receipt": receipt or {}, "prev": self.prev}
        line = json.dumps(o, sort_keys=True)
        with open(self.path, "a") as f:
            f.write(line + "\n")
        self.prev = hashlib.sha256(line.encode()).hexdigest()
        self.recs.append(o)
        return o

    # ---- views (projections of the log) ----
    def with_color(self, c):
        return [r for r in self.recs if c in r["colors"]]

    def heads(self, c):
        seen, out = set(), []
        for r in self.recs:
            if c in r["colors"] and r["head"] not in seen:
                seen.add(r["head"]); out.append(r["head"])
        return out

    def by_head(self, h):
        return [r for r in self.recs if r["head"] == h]

    def derives(self, color_ok=lambda cs: True):
        """Least closure over the log: a head is derived when some
        admitted record has all its premises derived (Canon.Derives
        with roots as zero-premise records)."""
        D, changed = set(), True
        adm = [r for r in self.recs if color_ok(r["colors"])]
        while changed:
            changed = False
            for r in adm:
                if r["head"] not in D and all(p in D for p in r["premises"]):
                    D.add(r["head"]); changed = True
        return D

def sha(path):
    return hashlib.sha256(open(path, "rb").read()).hexdigest()
