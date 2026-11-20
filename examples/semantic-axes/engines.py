# Closure and front engines with the capabilities the semantic axes
# measure: witnesses (visibility), single-level undo (reversibility),
# and merge of two independently built states (compositionality).
# Each capability is a component; a candidate is a product of
# components. Do-nothing and gamed controls are candidates too.
#
# Work counting: every engine counts premise ops exactly as PR 7's
# closure.py does (one read of a premise occurrence against derived
# state, a counter decrement, or a watch-scan test), plus one unit per
# element copied (snapshots) and per waiter entry moved (merges).
# Derived-state reads are also counted independently by the harness
# through CSet, which candidates cannot bypass without leaving D.
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "algorithm-search"))
from closure import admits

class CSet(set):
    """Derived set whose membership tests the harness counts."""
    def __init__(self, *a):
        super().__init__(*a); self.reads = 0
    def __contains__(self, x):
        self.reads += 1
        return set.__contains__(self, x)

def dprem(rec):
    seen, out = set(), []
    for x in rec[3]:
        if x not in seen:
            seen.add(x); out.append(x)
    return out

# ------------------------------------------------------------------
# Closure engines
# ------------------------------------------------------------------
class Counter:
    """Dowling-Gallier counters (proved in proof/Worklist.lean)."""
    name = "counter"
    def __init__(self, undo="none", witness="on", firsthead=False, lastwitness=False):
        self.D = CSet(); self.ops = 0; self.lastwitness = lastwitness; self.k = 0
        self.waiters, self.count, self.heads, self.ridx = {}, [], [], []
        self.wit = {}
        self.undo, self.witness_on, self.firsthead = undo, witness == "on", firsthead
        self.first = {}       # gaming control: first record index per head
        self.j = None         # journal of the last append
        self.snap = None
    # -- state copy for the snapshot control (cost counted) --
    def _copy(self):
        st = (set(self.D), {k: list(v) for k, v in self.waiters.items()}, list(self.count),
              list(self.heads), list(self.ridx), dict(self.wit))
        self.ops += len(self.D) + sum(len(v) for v in self.waiters.values()) + 3 * len(self.count) + len(self.wit)
        return st
    def _restore(self, st):
        D, w, c, h, r, wit = st
        self.D = CSet(D); self.waiters, self.count, self.heads, self.ridx, self.wit = w, c, h, r, wit
    def _log(self, *e):
        if self.j is not None:
            self.j.append(e)
    def append(self, rec, k):
        if self.undo == "snapshot":
            self.snap = self._copy()
        elif self.undo == "journal":
            self.j = []
        new = []
        self.k = k
        self.first.setdefault(rec[4], k)
        if not admits(rec):
            self._log("noop")
            return new
        ps, h = dprem(rec), rec[4]
        i = len(self.count)
        missing = 0
        for p in ps:
            self.ops += 1
            if p not in self.D:
                missing += 1
                self.waiters.setdefault(p, []).append(i); self._log("w", p)
        self.count.append(missing); self.heads.append(h); self.ridx.append(k); self._log("r")
        queue = []
        if missing == 0 and h not in self.D:
            self._fire(h, i, new, queue)
        while queue:
            t = queue.pop()
            ws = self.waiters.pop(t, None)
            if ws is None:
                continue
            self._log("wp", t, ws)
            for j in ws:
                self.ops += 1
                self.count[j] -= 1; self._log("c", j)
                if self.count[j] == 0 and self.heads[j] not in self.D:
                    self._fire(self.heads[j], j, new, queue)
        return new
    def _fire(self, g, j, new, queue):
        self.D.add(g); self._log("d", g)
        if self.witness_on:
            self.wit[g] = self.k if self.lastwitness else (self.first[g] if self.firsthead else self.ridx[j]); self._log("wit", g)
        new.append(g); queue.append(g)
    def undo_last(self):
        if self.undo == "snapshot":
            self._restore(self.snap); return True
        if self.undo != "journal" or self.j is None:
            return False
        for e in reversed(self.j):
            self.ops += 1
            tag = e[0]
            if tag == "w":
                self.waiters[e[1]].pop()
                if not self.waiters[e[1]]: del self.waiters[e[1]]
            elif tag == "r":
                self.count.pop(); self.heads.pop(); self.ridx.pop()
            elif tag == "wp":
                self.waiters[e[1]] = e[2]
            elif tag == "c":
                self.count[e[1]] += 1
            elif tag == "d":
                set.discard(self.D, e[1])
            elif tag == "wit":
                del self.wit[e[1]]
        self.j = None
        return True

class Watch(Counter):
    """Watched-premise closure (new in PR 7): each pending rule watches one
    missing premise and scans forward when it is derived."""
    name = "watch"
    def __init__(self, undo="none", witness="on", firsthead=False):
        super().__init__(undo, witness, firsthead)
        self.watch, self.prs, self.pos = {}, [], []
    def _copy(self):
        st = (set(self.D), {k: list(v) for k, v in self.watch.items()}, [list(p) for p in self.prs],
              list(self.pos), list(self.heads), list(self.ridx), dict(self.wit))
        self.ops += len(self.D) + sum(len(v) for v in self.watch.values()) + sum(len(p) for p in self.prs) + 3 * len(self.pos) + len(self.wit)
        return st
    def _restore(self, st):
        D, w, prs, pos, h, r, wit = st
        self.D = CSet(D); self.watch, self.prs, self.pos, self.heads, self.ridx, self.wit = w, prs, pos, h, r, wit
    def _scan(self, j):
        ps, k = self.prs[j], self.pos[j]
        old = k
        while k < len(ps):
            self.ops += 1
            if ps[k] not in self.D:
                if k != old: self._log("pos", j, old)
                self.pos[j] = k
                self.watch.setdefault(ps[k], []).append(j); self._log("w", ps[k])
                return False
            k += 1
        if k != old: self._log("pos", j, old)
        self.pos[j] = k
        return True
    def append(self, rec, k):
        if self.undo == "snapshot":
            self.snap = self._copy()
        elif self.undo == "journal":
            self.j = []
        new = []
        self.first.setdefault(rec[4], k)
        if not admits(rec):
            self._log("noop"); return new
        ps, h = list(rec[3]), rec[4]
        j = len(self.prs)
        self.prs.append(ps); self.pos.append(0); self.heads.append(h); self.ridx.append(k); self._log("r")
        queue = []
        if self._scan(j) and h not in self.D:
            self._fire(h, j, new, queue)
        self._drain(queue, new)
        return new
    def _drain(self, queue, new):
        while queue:
            t = queue.pop()
            ws = self.watch.pop(t, None)
            if ws is None:
                continue
            self._log("wp", t, ws)
            for j in ws:
                self._log("pos", j, self.pos[j])
                self.pos[j] += 1
                if self._scan(j) and self.heads[j] not in self.D:
                    self._fire(self.heads[j], j, new, queue)
    def undo_last(self):
        if self.undo == "snapshot":
            self._restore(self.snap); return True
        if self.undo != "journal" or self.j is None:
            return False
        for e in reversed(self.j):
            self.ops += 1
            tag = e[0]
            if tag == "w":
                self.watch[e[1]].pop()
                if not self.watch[e[1]]: del self.watch[e[1]]
            elif tag == "r":
                self.prs.pop(); self.pos.pop(); self.heads.pop(); self.ridx.pop()
            elif tag == "wp":
                self.watch[e[1]] = e[2]
            elif tag == "pos":
                self.pos[e[1]] = e[2]
            elif tag == "d":
                set.discard(self.D, e[1])
            elif tag == "wit":
                del self.wit[e[1]]
        self.j = None
        return True

class Rounds:
    """Naive rounds from the current set (PR 7, dominated on ops); kept as
    the simplest engine with a trivially correct merge."""
    name = "rounds"
    def __init__(self, undo="none", witness="on", firsthead=False):
        self.D = CSet(); self.ops = 0; self.rules = []; self.wit = {}
        self.undo, self.witness_on = undo, witness == "on"
        self.snap = None
    def append(self, rec, k):
        if self.undo == "snapshot":
            self.snap = (set(self.D), list(self.rules), dict(self.wit)); self.ops += len(self.D) + len(self.rules) + len(self.wit)
        if admits(rec):
            self.rules.append((dprem(rec), rec[4], k))
        return self._close()
    def _close(self):
        new, changed = [], True
        while changed:
            changed = False
            for ps, h, k in self.rules:
                if h in self.D:
                    continue
                ok = True
                for p in ps:
                    self.ops += 1
                    if p not in self.D:
                        ok = False; break
                if ok:
                    self.D.add(h); new.append(h); changed = True
                    if self.witness_on: self.wit[h] = k
        return new
    def undo_last(self):
        if self.undo == "snapshot":
            D, r, w = self.snap; self.D = CSet(D); self.rules, self.wit = r, w; return True
        return False

class Null:
    """Do-nothing control: derives nothing, witnesses nothing, merges by
    returning its left state, undoes by doing nothing."""
    name = "null"
    def __init__(self, **kw):
        self.D = CSet(); self.ops = 0; self.wit = {}
    def append(self, rec, k):
        return []
    def undo_last(self):
        return True

class Lookahead(Counter):
    """Gamed control: reads the whole trace up front (it is handed the
    future) and reports every eventually derivable term at the first
    append. Zero work per append afterwards."""
    name = "lookahead"
    def __init__(self, future=None, **kw):
        super().__init__(**kw)
        self.future, self.done = future, False
    def append(self, rec, k):
        if self.done:
            return []
        self.done = True
        c = Counter()
        for i, r in enumerate(self.future):
            c.append(r, i)
        self.D = CSet(set(c.D)); self.wit = dict(c.wit)
        return list(c.D)

ENGINES = {"counter": Counter, "watch": Watch, "rounds": Rounds}

# ---------------- merges (compositionality) ----------------
def merge(kind, A, B, offset, rebuild):
    """Merge two states built independently over logs LA and LB (B's
    record indexes shifted by `offset`). kind:
      propagate  reuse both states: D = DA | DB, then wake only rules
                 pending on a term the other side derived
      recompute  gamed control: rebuild from empty over LA ++ LB
      left       do-nothing control: return A unchanged
    Returns (state, ops)."""
    if kind == "left":
        return A, 0
    if kind == "recompute":
        s = rebuild()
        return s, s.ops
    ops0 = A.ops + B.ops
    if isinstance(A, Rounds):
        s = Rounds(witness="on" if A.witness_on else "off")
        s.rules = A.rules + [(ps, h, k + offset) for ps, h, k in B.rules]
        s.D = CSet(set(A.D) | set(B.D)); s.wit = {**{h: k + offset for h, k in B.wit.items()}, **A.wit}
        s.ops = len(B.rules) + len(B.D)
        s._close()
        return s, s.ops
    s = type(A)(witness="on" if A.witness_on else "off")
    n = len(A.heads)
    s.ops = 0
    s.heads = A.heads + B.heads
    s.ridx = A.ridx + [k + offset for k in B.ridx]
    s.D = CSet(set(A.D) | set(B.D))
    s.wit = {**{h: k + offset for h, k in B.wit.items()}, **A.wit}
    s.ops += len(B.heads) + len(B.D)
    if isinstance(A, Watch):
        s.prs = A.prs + B.prs; s.pos = A.pos + B.pos
        s.watch = {t: list(v) for t, v in A.watch.items()}
        for t, v in B.watch.items():
            s.watch.setdefault(t, []).extend(j + n for j in v); s.ops += len(v)
        wake = (set(B.D) - set(A.D)) | (set(A.D) - set(B.D))
        new, queue = [], list(wake)
        s._drain(queue, new)
        return s, s.ops
    s.count = A.count + B.count
    s.waiters = {t: list(v) for t, v in A.waiters.items()}
    for t, v in B.waiters.items():
        s.waiters.setdefault(t, []).extend(j + n for j in v); s.ops += len(v)
    # wake pending rules on terms derived by the other side
    queue = list((set(B.D) - set(A.D)) | (set(A.D) - set(B.D)))
    new = []
    while queue:
        t = queue.pop()
        for j in s.waiters.pop(t, ()):
            s.ops += 1
            s.count[j] -= 1
            if s.count[j] == 0 and s.heads[j] not in s.D:
                s._fire(s.heads[j], j, new, queue)
    return s, s.ops

# ------------------------------------------------------------------
# Front engines (archive) with witnesses, undo and merge
# ------------------------------------------------------------------
def dominates(a, b, ops):
    ops[0] += 1
    return a != b and all(x <= y for x, y in zip(a, b))

class Archive:
    """Online Pareto archive (proved: AlgoSearch.mem_arch).
    undo: none | snapshot | residual (keep what an insert removed, the
    retained residual of Chris's reversible result) | recompute.
    witness: for each rejected or removed point, a member that dominates it."""
    def __init__(self, undo="none", witness="on"):
        self.m = {}; self.ops = [0]; self.wit = {}; self.seen = []
        self.undo, self.witness_on = undo, witness == "on"
        self.last = None
    def insert(self, i, a):
        self.seen.append((i, a))
        if self.undo == "snapshot":
            self.last = (dict(self.m), dict(self.wit)); self.ops[0] += len(self.m) + len(self.wit)
        for j, b in self.m.items():
            if dominates(b, a, self.ops):
                if self.witness_on: self.wit[i] = j
                self.last = ("rejected", i) if self.undo == "residual" else self.last
                return
        removed = []
        for j, b in list(self.m.items()):
            if dominates(a, b, self.ops):
                removed.append((j, b)); del self.m[j]
                if self.witness_on: self.wit[j] = i
        self.m[i] = a
        if self.undo == "residual":
            self.last = ("inserted", i, removed)
    def undo_last(self):
        i, a = self.seen.pop()
        if self.undo == "snapshot":
            self.m, self.wit = self.last; return True
        if self.undo == "residual":
            if self.last[0] == "rejected":
                self.wit.pop(i, None)
            else:
                _, i, removed = self.last
                del self.m[i]
                for j, b in removed:
                    self.m[j] = b; self.wit.pop(j, None); self.ops[0] += 1
            return True
        if self.undo == "recompute":
            seen = self.seen
            self.m, self.wit, self.seen = {}, {}, []
            u, self.undo = self.undo, "none"
            for j, b in seen:
                self.insert(j, b)
            self.undo = u
            return True
        return False
