"""Abduction engine over the canonical hypergraph (one append-only record log).

Semantics are those of proof/Abduction.lean: a hypothesis H is a set of abducible terms
appended as root records; H explains observations O when every o in O is derivable and the
reserved term `bot` is not. Negative observations are records whose head is `bot`.

Three independent pieces live here:
  * Log: the hash-chained record log with a symbol table (terms are ints in the Lean files).
  * ATMS: incremental label propagation. label[a] is the set of minimal consistent
    environments (sets of abducibles, size <= k) that derive a. Records are appended one at a
    time; only the labels downstream of a change are recomputed. Nogoods (environments that
    derive bot) are pruned everywhere as soon as they appear.
  * brute(): the reference enumerator, a line-by-line mirror of Lean's `abduce` (every
    sublist of A up to size k, `minimalB` by erase-one), used to check ATMS completeness.
"""
import hashlib, itertools, json
from collections import defaultdict

BOT = "⊥"


def sha(b):
    return hashlib.sha256(b if isinstance(b, bytes) else b.encode()).hexdigest()


class Log:
    """One record log. Records: (id, level, colors, premises, head) over interned terms."""

    def __init__(self):
        self.names, self.ids, self.recs = [], {}, []
        self.chain = []  # hash chain over the canonical JSON of each appended record
        self.atom(BOT)  # term 0 is bot

    def atom(self, name):
        if name not in self.ids:
            self.ids[name] = len(self.names)
            self.names.append(name)
        return self.ids[name]

    def add(self, premises, head, colors=(), level=0, **meta):
        rec = {"id": len(self.recs), "level": level, "colors": list(colors),
               "premises": [self.atom(p) for p in premises], "head": self.atom(head)}
        self.recs.append(rec)
        prev = self.chain[-1] if self.chain else "0" * 64
        body = json.dumps({"prev": prev, "rec": rec, "names": [self.names[x] for x in rec["premises"]] + [self.names[rec["head"]]], "meta": meta}, sort_keys=True)
        self.chain.append(sha(body))
        return rec

    def head_hash(self):
        return self.chain[-1] if self.chain else "0" * 64


def closure(recs, roots, counter=None):
    """Least closure under records (premise counters, each term processed once)."""
    S = set(roots)
    left, by_prem, stack = {}, defaultdict(list), list(S)
    for i, r in enumerate(recs):
        ps = set(r["premises"])
        left[i] = len(ps)
        for p in ps:
            by_prem[p].append(i)
        if not ps and r["head"] not in S:
            S.add(r["head"]); stack.append(r["head"])
    while stack:
        a = stack.pop()
        for i in by_prem.get(a, ()):
            if counter is not None:
                counter[0] += 1
            left[i] -= 1
            if left[i] == 0 and recs[i]["head"] not in S:
                S.add(recs[i]["head"]); stack.append(recs[i]["head"])
    return S


def closure_naive(recs, roots):
    S = set(roots); ch = True
    while ch:
        ch = False
        for r in recs:
            if r["head"] not in S and all(p in S for p in r["premises"]):
                S.add(r["head"]); ch = True
    return S


def explains(recs, A, O, H, bot=0):
    S = closure(recs, H)
    return all(h in A for h in H) and all(o in S for o in O) and bot not in S


def minimal(recs, A, O, H, bot=0):
    """Mirror of Lean `minimalB`: duplicate free, explains, no erase-one subset explains."""
    if len(set(H)) != len(H) or not explains(recs, A, O, H, bot):
        return False
    return all(not explains(recs, A, O, [y for y in H if y != x], bot) for x in H)


def brute(recs, A, O, k, bot=0):
    """Mirror of Lean `abduce`: every sublist of A of length <= k that is minimal."""
    out = []
    for n in range(0, k + 1):
        for H in itertools.combinations(A, n):
            if minimal(recs, A, O, list(H), bot):
                out.append(frozenset(H))
    return set(out)


def minimize(envs):
    """Keep the subset-minimal environments."""
    envs = sorted(set(envs), key=len)
    out = []
    for e in envs:
        if not any(f <= e for f in out):
            out.append(e)
    return out


class ATMS:
    """Incremental bounded label propagation over appended records."""

    def __init__(self, abducibles, k, bot=0):
        self.k, self.bot = k, bot
        self.A = set(abducibles)
        self.label = defaultdict(list)
        self.nogoods = []
        self.recs = []
        self.by_prem = defaultdict(list)
        self.ops = defaultdict(int)
        for a in sorted(self.A):
            self.label[a] = [frozenset([a])]

    def consistent(self, e):
        return not any(n <= e for n in self.nogoods)

    def _combine(self, rec):
        cur = [frozenset()]
        for p in dict.fromkeys(rec["premises"]):
            lp = self.label.get(p, [])
            if not lp:
                return []
            nxt = []
            for e in cur:
                for f in lp:
                    self.ops["union"] += 1
                    u = e | f
                    if len(u) <= self.k and self.consistent(u):
                        nxt.append(u)
            cur = minimize(nxt)
            if not cur:
                return []
        return cur

    def _merge(self, a, envs):
        """Add envs to label[a]; return True if the label changed."""
        old = self.label.get(a, [])
        new = minimize(old + envs)
        if set(new) == set(old):
            return False
        self.label[a] = new
        return True

    def _prune(self):
        for a in list(self.label):
            kept = [e for e in self.label[a] if self.consistent(e)]
            if len(kept) != len(self.label[a]):
                self.label[a] = kept

    def add(self, rec):
        i = len(self.recs)
        self.recs.append(rec)
        for p in set(rec["premises"]):
            self.by_prem[p].append(i)
        self._propagate([i])

    def _propagate(self, todo):
        todo = list(todo)
        seen_round = 0
        while todo:
            i = todo.pop()
            self.ops["visit"] += 1
            rec = self.recs[i]
            envs = self._combine(rec)
            if not envs:
                continue
            h = rec["head"]
            if h == self.bot:
                before = list(self.nogoods)
                self.nogoods = minimize(self.nogoods + envs)
                if set(self.nogoods) != set(before):
                    self._prune()
                    # a pruned label can only shrink; downstream labels built from pruned
                    # environments are pruned by the same test, so nothing to re-propagate.
                continue
            if self._merge(h, envs):
                todo.extend(self.by_prem.get(h, ()))
            seen_round += 1

    def explanations(self, O):
        """Minimal consistent environments deriving every o in O, size <= k."""
        cur = [frozenset()]
        for o in dict.fromkeys(O):
            lo = self.label.get(o, [])
            nxt = [e | f for e in cur for f in lo if len(e | f) <= self.k and self.consistent(e | f)]
            cur = minimize(nxt)
            if not cur:
                return []
        return cur


def front(cands):
    """Pareto front over (cover up, cost down); cands: list of (key, cover, cost)."""
    def dom(y, x):
        return y[1] >= x[1] and y[2] <= x[2] and (y[1] > x[1] or y[2] < x[2])
    return [x for x in cands if not any(dom(y, x) for y in cands)]
