# Family (a): incremental closure of the canonical log.
#
# Task (same for every candidate): records arrive one at a time; after
# each append the candidate reports the terms that became derivable in
# viewC ch L r q (level r = 0, identity chain, color test `live`). The
# derived set after append k must equal the least closure of the first
# k admitted records (proof/Canon.lean viewC, proof/Worklist.lean
# mem_prefix).
#
# Candidates are generated from components, not written one by one:
#   trigger  scratch | rounds | delta | counter | watch
#   dedup    on | off          (premises deduplicated at admission)
#   check    short | full      (readiness test stops at the first
#                               missing premise, or reads them all;
#                               only meaningful for scratch/rounds/delta)
# Counted unit, identical for all: one "premise op" is one read of a
# premise occurrence against the derived state (a membership test, a
# counter decrement on a waiter visit, or a watch-scan test).

LIVE_DROP = (4, 5, 7)  # disqualified, demanded, proposal (Space.lean `live`)

def admits(rec, r=0):
    _id, level, colors, prem, head = rec
    return level <= r and not any(c in colors for c in LIVE_DROP)

class Base:
    def __init__(self, dedup, check):
        self.dedup, self.short = dedup == "on", check == "short"
        self.D = set()
        self.ops = 0
        self.rules = []          # admitted (premises, head)

    def prem(self, rec):
        p = rec[3]
        if self.dedup:
            seen, out = set(), []
            for x in p:
                if x not in seen:
                    seen.add(x); out.append(x)
            return out
        return list(p)

    def ready(self, ps, D):
        ok = True
        if self.short:
            for p in ps:
                self.ops += 1
                if p not in D:
                    return False
            return True
        for p in ps:
            self.ops += 1
            if p not in D:
                ok = False
        return ok

class Scratch(Base):
    """Recompute the least closure from empty after every append."""
    def append(self, rec):
        if admits(rec):
            self.rules.append((self.prem(rec), rec[4]))
        D, changed = set(), True
        while changed:
            changed = False
            for ps, h in self.rules:
                if h not in D and self.ready(ps, D):
                    D.add(h); changed = True
        new = D - self.D
        self.D = D
        return new

class Rounds(Base):
    """Continue from the current derived set; rounds over all admitted rules."""
    def append(self, rec):
        if admits(rec):
            self.rules.append((self.prem(rec), rec[4]))
        D, new, changed = self.D, set(), True
        while changed:
            changed = False
            for ps, h in self.rules:
                if h not in D and self.ready(ps, D):
                    D.add(h); new.add(h); changed = True
        return new

class Delta(Base):
    """Semi-naive: after an append, re-examine only rules that have a
    premise among the terms derived in the last step (term -> rules index)."""
    def __init__(self, dedup, check):
        super().__init__(dedup, check)
        self.index = {}
    def append(self, rec):
        new = set()
        if not admits(rec):
            return new
        ps, h = self.prem(rec), rec[4]
        self.rules.append((ps, h))
        for p in set(ps):
            self.index.setdefault(p, []).append((ps, h))
        D = self.D
        frontier = []
        if h not in D and self.ready(ps, D):
            D.add(h); new.add(h); frontier.append(h)
        while frontier:
            nxt = []
            for t in frontier:
                for qs, g in self.index.get(t, ()):
                    if g not in D and self.ready(qs, D):
                        D.add(g); new.add(g); nxt.append(g)
            frontier = nxt
        return new

class Counter(Base):
    """Dowling-Gallier counters: per rule the number of missing premise
    occurrences, term -> waiting rules, each derived term visited once.
    The proved candidate (proof/Worklist.lean, c49c546) is dedup=on."""
    def __init__(self, dedup, check):
        super().__init__(dedup, check)
        self.waiters, self.count, self.heads = {}, [], []
    def append(self, rec):
        new = set()
        if not admits(rec):
            return new
        ps, h = self.prem(rec), rec[4]
        i = len(self.count)
        missing = 0
        for p in ps:
            self.ops += 1
            if p not in self.D:
                missing += 1
                self.waiters.setdefault(p, []).append(i)
        self.count.append(missing); self.heads.append(h)
        queue = []
        if missing == 0 and h not in self.D:
            self.D.add(h); new.add(h); queue.append(h)
        while queue:
            t = queue.pop()
            for j in self.waiters.pop(t, ()):
                self.ops += 1
                self.count[j] -= 1
                if self.count[j] == 0:
                    g = self.heads[j]
                    if g not in self.D:
                        self.D.add(g); new.add(g); queue.append(g)
        return new

class Watch(Base):
    """New variant (Horn form of two-watched-literals): each pending rule
    watches one missing premise; when it is derived the rule scans
    forward for the next missing premise, firing if none is left.
    No counters, one waiter entry per pending rule."""
    def __init__(self, dedup, check):
        super().__init__(dedup, check)
        self.watch = {}
        self.prs, self.pos, self.heads = [], [], []
    def scan(self, j):
        ps, k = self.prs[j], self.pos[j]
        while k < len(ps):
            self.ops += 1
            if ps[k] not in self.D:
                self.pos[j] = k
                self.watch.setdefault(ps[k], []).append(j)
                return False
            k += 1
        self.pos[j] = k
        return True
    def append(self, rec):
        new = set()
        if not admits(rec):
            return new
        ps, h = self.prem(rec), rec[4]
        j = len(self.prs)
        self.prs.append(ps); self.pos.append(0); self.heads.append(h)
        queue = []
        if self.scan(j) and h not in self.D:
            self.D.add(h); new.add(h); queue.append(h)
        while queue:
            t = queue.pop()
            for j in self.watch.pop(t, ()):
                self.pos[j] += 1  # the watched premise is now derived
                if self.scan(j):
                    g = self.heads[j]
                    if g not in self.D:
                        self.D.add(g); new.add(g); queue.append(g)
        return new

TRIGGERS = {"scratch": Scratch, "rounds": Rounds, "delta": Delta,
            "counter": Counter, "watch": Watch}

def make(trigger, dedup, check):
    return TRIGGERS[trigger](dedup, check)

def earliest(trace, r=0):
    """Independent reference (Knuth 1977 superior-function shortest
    path): e(t) = least append index after which t is derivable.
    D_k = {t : e(t) <= k}. Uses distinct premises; not a candidate."""
    import heapq
    rules, waiting = [], {}
    heap = []
    for k, rec in enumerate(trace):
        if not admits(rec, r):
            continue
        ps = sorted(set(rec[3]))
        j = len(rules)
        rules.append([k, len(ps), rec[4]])
        if not ps:
            heapq.heappush(heap, (k, rec[4]))
        for p in ps:
            waiting.setdefault(p, []).append(j)
    e = {}
    while heap:
        t_time, t = heapq.heappop(heap)
        if t in e:
            continue
        e[t] = t_time
        for j in waiting.get(t, ()):
            rules[j][1] -= 1
            if rules[j][1] == 0:
                heapq.heappush(heap, (max(rules[j][0], t_time), rules[j][2]))
    return e
