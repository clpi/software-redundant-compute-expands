# Families (b)-(e): fronts, selection, stop rules, incremental
# re-scoring, and the weight meta-search. All costs are minimized.
# Counted unit "op": one vector dominance test, one vector addition,
# one scalarized evaluation, or one heap push, as each function states.
import heapq, itertools

class Ops:
    def __init__(self): self.n = 0

def dominates(a, b, ops):
    ops.n += 1
    le = all(x <= y for x, y in zip(a, b))
    return le and a != b

# ---------------- (b1) static front ----------------
def front_pairwise(items, ops):
    """Definition-shaped: keep a iff no b dominates it. items: [(id, vec)]."""
    out = []
    for i, a in items:
        if not any(dominates(b, a, ops) for j, b in items if j != i):
            out.append(i)
    return set(out)

def front_sortfilter(items, ops):
    """Sort by coordinate sum (a dominator has a strictly smaller sum),
    compare only against kept members with smaller sum."""
    srt = sorted(items, key=lambda t: (sum(t[1]), t[1], t[0]))
    kept = []
    for i, a in srt:
        sa = sum(a)
        if not any(sum(b) < sa and dominates(b, a, ops) for _, b in kept):
            kept.append((i, a))
    return {i for i, _ in kept}

class Archive:
    """(d) Online front: insert compares only against current members."""
    def __init__(self): self.m = {}
    def insert(self, i, a, ops):
        for j, b in list(self.m.items()):
            if dominates(b, a, ops):
                return
        for j, b in list(self.m.items()):
            if dominates(a, b, ops):
                del self.m[j]
        self.m[i] = a

# ---------------- (b2) joint-plan fronts (additive factors) ----------------
def add(u, v, ops):
    ops.n += 1
    return tuple(x + y for x, y in zip(u, v))

def plans_brute(factors, ops, prune=False):
    fs = [[o for o in f] for f in factors]
    if prune:
        fs = [[f[k] for k in sorted(front_sortfilter(list(enumerate(f)), ops))] for f in fs]
    items = []
    for combo in itertools.product(*fs):
        v = combo[0]
        for w in combo[1:]:
            v = add(v, w, ops)
        items.append((len(items), v))
    vals = {i: v for i, v in items}
    return {vals[i] for i in front_sortfilter(items, ops)}

def plans_fold(factors, ops, prune=True):
    """Sequential Pareto merge: P <- front(P (+) front(F))."""
    P = [tuple(0 for _ in factors[0][0])]
    for f in factors:
        g = [f[k] for k in sorted(front_sortfilter(list(enumerate(f)), ops))] if prune else f
        items = [(n, add(p, q, ops)) for n, (p, q) in enumerate(itertools.product(P, g))]
        keep = front_sortfilter(items, ops)
        P = sorted({items[k][1] for k in keep})
    return set(P)

# ---------------- (b3) selection rules ----------------
def normalize(vecs):
    d = len(vecs[0])
    z = [min(v[i] for v in vecs) for i in range(d)]
    n = [max(v[i] for v in vecs) for i in range(d)]
    return z, [max(n[i] - z[i], 1) for i in range(d)]

def scal(rule, v, w, z, s, rho=1e-4):
    x = [(v[i] - z[i]) / s[i] for i in range(len(v))]
    if rule == "ws":
        return sum(wi * xi for wi, xi in zip(w, x))
    if rule == "ch":
        return max(wi * xi for wi, xi in zip(w, x))
    if rule == "ach":
        return max(wi * xi for wi, xi in zip(w, x)) + rho * sum(x)
    raise ValueError(rule)

def pick(rule, items, w, ops, frame):
    """items: [(id, vec)]; frame = (z, s) fixed per dataset so direct and
    front-first scalarize identically. Ties broken by (vec, id)."""
    z, s = frame
    best = None
    for i, v in items:
        ops.n += 1
        if rule == "eps":
            x = [(v[k] - z[k]) / s[k] for k in range(len(v))]
            if any(x[k] > w[k] for k in range(1, len(v))):
                continue
            key = (x[0], v, i)
        elif rule == "lex":
            key = (tuple(v[k] for k in w), v, i)
        else:
            key = (scal(rule, v, w, z, s), v, i)
        if best is None or key < best[0]:
            best = (key, i)
    return None if best is None else best[1]

def simplex(d, steps, lo=1):
    """Weights on the simplex grid with denominator `steps` (positive when lo=1)."""
    out = []
    for c in itertools.product(range(lo, steps + (1 - lo)), repeat=d - 1):
        if sum(c) <= steps - lo:
            out.append(tuple(x / steps for x in c + (steps - sum(c),)))
    return out

def eps_grid(d, steps):
    return [(0.0,) + c for c in itertools.product([k / steps for k in range(steps + 1)], repeat=d - 1)]

def solved_weights(p, frame, eta=1e-9):
    """Chebyshev weights aimed at p: w_i proportional to 1/(p_i - z_i + eta)."""
    z, s = frame
    x = [(p[i] - z[i]) / s[i] + eta for i in range(len(p))]
    w = [1 / xi for xi in x]
    t = sum(w)
    return tuple(wi / t for wi in w)

# ---------------- (c) stop rules on a plan stream ----------------
def plan_score_parts(factors, w):
    """Additive normalized score: per objective, scale = sum over factors
    of (max - min); score(plan) = sum_f sum_i w_i (c_fi - min_fi)/scale_i.
    Returns per-factor per-option scores (each >= 0)."""
    d = len(factors[0][0])
    scale = [max(sum(max(o[i] for o in f) - min(o[i] for o in f) for f in factors), 1) for i in range(d)]
    mins = [[min(o[i] for o in f) for i in range(d)] for f in factors]
    return [[sum(w[i] * (o[i] - mins[k][i]) / scale[i] for i in range(d)) for o in f] for k, f in enumerate(factors)]

def stop_stream(parts, rule, delta=None, ops=None):
    """Plans in lexicographic order of option indices. Returns
    (picked index tuple, picked score, examined, certified)."""
    m = len(parts)
    best, bscore, n = None, None, 0
    # suffix sums of per-factor minima, for the remaining-set bound
    fmin = [min(p) for p in parts]
    suf = [0.0] * (m + 1)
    for k in range(m - 1, -1, -1):
        suf[k] = suf[k + 1] + fmin[k]
    # min over options strictly after index c in factor k
    after = [[min(p[c + 1:]) if c + 1 < len(p) else float("inf") for c in range(len(p))] for p in parts]
    total = 1
    for p in parts:
        total *= len(p)
    for combo in itertools.product(*[range(len(p)) for p in parts]):
        n += 1; ops.n += 1
        sc = sum(parts[k][c] for k, c in enumerate(combo))
        if bscore is None or sc < bscore:
            best, bscore = combo, sc
        if rule == "threshold" and bscore <= delta:
            return best, bscore, n, False
        if rule == "bound":
            # remaining plans: same prefix up to k-1, larger option at k, anything after
            lb, pre = float("inf"), 0.0
            for k, c in enumerate(combo):
                ops.n += 1
                lb = min(lb, pre + after[k][c] + suf[k + 1])
                pre += parts[k][c]
            if bscore <= lb:
                return best, bscore, n, True
    return best, bscore, n, True  # exhaustive: every plan seen

def stop_bestfirst(parts, ops):
    """k-best enumeration in score order (sorted factors, heap of
    successors); the first popped plan is optimal and certified."""
    order = [sorted(range(len(p)), key=lambda c: (p[c], c)) for p in parts]
    start = tuple(0 for _ in parts)
    sc = sum(parts[k][order[k][0]] for k in range(len(parts)))
    heap = [(sc, start)]
    ops.n += sum(len(p) for p in parts)  # every option scored once to sort its factor
    sc, pos = heapq.heappop(heap)
    return tuple(order[k][pos[k]] for k in range(len(parts))), sc, 1, True
