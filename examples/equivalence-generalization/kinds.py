"""Eight kinds of software, each with an executable semantics.

Every kind gives: programs, observers (each an equivalence over
behavior, or a tolerance relation), increasing measurement
resolutions, a truth universe larger than any resolution, contexts
with a declared compositionality table, and an observe function.

A resolution is (name, inputs, exhaustive) where exhaustive is True
only when the inputs are the whole declared input domain. Schedules
are either "one" (a single deterministic run, what a plain test run
gives) or "all" (every schedule the kind's environment allows; these
are finite for every program here).

Truth is computed on the universe with all schedules. The universe
is finite, so truth is truth relative to it; for kinds whose domain
is infinite, the qualified policy makes no bare join at all, so its
soundness does not lean on the universe.
"""

import itertools
import math
import struct

RUNS = [0]


def tick(n=1):
    RUNS[0] += n


# ---------------------------------------------------------------- pure

def wrap8(v):
    return ((v + 128) % 256) - 128


class Pure:
    name = "pure functions (8-bit integers)"
    finite = True
    finest = "out"
    observers = {"out": "eq"}
    progs = {
        "absA": lambda x: x if x >= 0 else wrap8(-x),
        "absB": lambda x: wrap8((x ^ (x >> 7)) - (x >> 7)),
        "absC": lambda x: max(x, -x),               # 128 at -128: no wrap
        "dblA": lambda x: wrap8(x * 2),
        "dblB": lambda x: wrap8(x << 1),
        "dblC": lambda x: wrap8(x + x),
        "halfA": lambda x: x // 2,
        "halfB": lambda x: int(x / 2),              # truncates: differs on negative odd
        "clampA": lambda x: min(max(x, -100), 100),
        "clampB": lambda x: x if -100 <= x <= 100 else (100 if x > 0 else -100),
    }
    domain = list(range(-128, 128))
    resolutions = [
        ("r0", [0, 1, 2, 3, 5, 8, 13, 21, 50, 100], False),
        ("r1", list(range(-126, 128, 7)), False),
        ("r2", list(range(-128, 128)), True),
    ]
    universe = list(range(-128, 128))
    contexts = {"plus1": lambda f: (lambda x: wrap8(f(x) + 1))}
    compositional = {("out", "plus1"): True}

    def run(self, prog, inputs, sched, obs):
        f = prog
        tick(len(inputs))
        return tuple(f(x) for x in inputs)


# ------------------------------------------------------------ stateful

class Counter:
    def __init__(self, kind):
        self.kind, self.n, self.items, self.cache, self.writes = kind, 0, [], None, 0

    def call(self, op):
        k = self.kind
        if k == "A2":                     # same as A, stored negated
            if op == "inc":
                self.n -= 1; self.writes += 1; return None
            if op == "reset":
                self.n = 0; self.writes += 1; return None
            return -self.n
        if op == "inc":
            if k == "B":
                self.items.append(1); self.cache = None
            elif k == "C":
                self.n = min(self.n + 1, 4)
            else:
                self.n += 1
            self.writes += 1
            return None
        if op == "reset":
            if k == "B":
                self.items = []; self.cache = None; self.writes += 1
            elif k in ("D", "E"):
                if self.n:
                    self.n = 0; self.writes += 1
            else:
                self.n = 0; self.writes += 1
            return None
        # get
        if k == "B":
            if self.cache is None:
                self.cache = len(self.items); self.writes += 1
            return self.cache
        if k == "E":
            return self.n + 1
        return self.n


class Stateful:
    name = "stateful objects (method-call sequences)"
    finite = False
    finest = None
    observers = {"gets": "eq", "writes": "eq"}
    progs = {k: k for k in ("A", "A2", "B", "C", "D", "E")}

    @staticmethod
    def seqs(n):
        return [s for L in range(n + 1) for s in itertools.product(("inc", "get", "reset"), repeat=L)]

    resolutions = None
    universe = None
    contexts = {}
    compositional = {}

    def __init__(self):
        self.resolutions = [("r0", self.seqs(2), False), ("r1", self.seqs(4), False)]
        self.universe = self.seqs(6)

    def run(self, prog, inputs, sched, obs):
        out = []
        for s in inputs:
            c = Counter(prog)
            gets = tuple(r for r in (c.call(op) for op in s) if r is not None)
            out.append(gets if obs == "gets" else c.writes)
            tick()
        return tuple(out)


# ---------------------------------------------------------- concurrent

def exec_op(op, x, r):
    if op == "inc":
        return x + 1, r
    if op == "load":
        return x, x
    if op == "storeInc":
        return r + 1, r
    raise ValueError(op)


def interleavings(a, b):
    if not a:
        yield [("R", o) for o in b]; return
    if not b:
        yield [("L", o) for o in a]; return
    for rest in interleavings(a[1:], b):
        yield [("L", a[0])] + rest
    for rest in interleavings(a, b[1:]):
        yield [("R", b[0])] + rest


class Concurrent:
    name = "concurrent threads (shared memory)"
    finite = False
    finest = "final"
    observers = {"final": "eq"}
    # a program is a pair of thread programs run in parallel; a thread
    # alone is the pair with an empty second thread
    threads = {
        "atomic": ("inc",),
        "split": ("load", "storeInc"),
        "double": ("inc", "inc"),
    }
    progs = {name: (t, ()) for name, t in threads.items()}
    progs["sysA"] = (("inc",), ("inc",))
    progs["sysB"] = (("load", "storeInc"), ("load", "storeInc"))
    resolutions = [("r0", [0], False), ("r1", [0, 1, 2, 3], False)]
    universe = list(range(8))
    contexts = {"par": "par"}
    context_domain = ("atomic", "split", "double")   # single threads only
    compositional = {("final", "par"): False}

    def wrap(self, ctx, prog):
        a, _ = prog
        return (a, a)

    def run(self, prog, inputs, sched, obs):
        a, b = prog
        out = []
        for x0 in inputs:
            orders = list(interleavings(list(a), list(b)))
            if sched == "one":
                orders = orders[:1]          # thread one first, then thread two
            finals = set()
            for order in orders:
                x, r = x0, {"L": 0, "R": 0}
                for side, op in order:
                    x, r[side] = exec_op(op, x, r[side])
                finals.add(x)
                tick()
            out.append(tuple(sorted(finals)))
        return tuple(out)


# --------------------------------------------------------- distributed

class Distributed:
    name = "distributed replicas (reordering, duplicating network)"
    finite = False
    finest = "converged"
    observers = {"converged": "eq"}
    progs = {"gcounter": "g", "gcounter2": "g2", "sumdelta": "s", "lww": "l"}
    resolutions = [("r0", [(1, 1)], False), ("r1", [(1, 1), (1, 2), (2, 1)], False)]
    universe = [(a, b) for a in range(3) for b in range(3)]
    contexts = {}
    compositional = {}

    def replica_run(self, kind, incs, order):
        # two replicas; replica i does incs[i] local increments, each
        # broadcast as a message; `order` lists deliveries (msg index),
        # possibly with one duplicate
        if kind == "g2":                  # same CRDT, dict state, merged by key
            st = [{}, {}]
            msgs = []
            for i in range(2):
                for _ in range(incs[i]):
                    st[i][i] = st[i].get(i, 0) + 1
                    msgs.append((1 - i, dict(st[i])))
            for m in order:
                dst, payload = msgs[m]
                for key, val in payload.items():
                    st[dst][key] = max(st[dst].get(key, 0), val)
            return tuple(sum(s.values()) for s in st)
        st = []
        for i in range(2):
            if kind == "g":
                st.append([0, 0])
            elif kind == "s":
                st.append(0)
            else:
                st.append((0, -1, 0))   # (lamport, writer, value)
        msgs = []
        for i in range(2):
            for _ in range(incs[i]):
                if kind == "g":
                    st[i][i] += 1; msgs.append((1 - i, list(st[i])))
                elif kind == "s":
                    st[i] += 1; msgs.append((1 - i, 1))
                else:
                    ts, w, v = st[i]; st[i] = (ts + 1, i, v + 1); msgs.append((1 - i, st[i]))
        for m in order:
            dst, payload = msgs[m]
            if kind == "g":
                st[dst] = [max(a, b) for a, b in zip(st[dst], payload)]
            elif kind == "s":
                st[dst] += payload
            else:
                st[dst] = max(st[dst], payload)
        val = [sum(s) if kind == "g" else (s if kind == "s" else s[2]) for s in st]
        return tuple(val)

    def run(self, prog, inputs, sched, obs):
        out = []
        for incs in inputs:
            n = sum(incs)
            base = list(range(n))
            if sched == "one":
                orders = [base]
            else:
                orders = set()
                for perm in itertools.permutations(base):
                    orders.add(perm)
                    for d in base:            # one duplicated delivery
                        for pos in range(n + 1):
                            orders.add(perm[:pos] + (d,) + perm[pos:])
                orders = sorted(orders)
            res = set()
            for o in orders:
                res.add(self.replica_run(prog, incs, list(o)))
                tick()
            out.append(tuple(sorted(res)))
        return tuple(out)


# ---------------------------------------------------------------- float

def ieee_div(a, b):
    if b == 0.0:
        if a == 0.0 or math.isnan(a):
            return float("nan")
        return math.copysign(math.inf, a) * math.copysign(1.0, b)
    if math.isinf(a) and math.isinf(b):
        return float("nan")
    return a / b


def bits(v):
    return struct.pack(">d", v).hex()


def value(v):
    if math.isnan(v):
        return "nan"
    return 0.0 if v == 0.0 else v


def close(a, b, rel=1e-9):
    if math.isnan(a) or math.isnan(b):
        return math.isnan(a) and math.isnan(b)
    if math.isinf(a) or math.isinf(b):
        return a == b
    return abs(a - b) <= rel * max(abs(a), abs(b), 1e-300)


def safe(f):
    def g(x):
        try:
            return f(x)
        except (OverflowError, ValueError):
            return float("nan")
    return g


FLOAT_R0 = [1.0, 2.0, 0.5, 3.0, 10.0]
FLOAT_R1 = FLOAT_R0 + [-1.0, -2.5, 1e10, 1e-10, 123.456]
FLOAT_U = FLOAT_R1 + [0.0, -0.0, math.inf, -math.inf, float("nan"), 1e308, -1e308, 5e-324, 1e200]


class Float:
    name = "numeric (IEEE-754 doubles)"
    finite = False
    finest = "bits"
    observers = {"bits": "eq", "value": "eq", "near": "tol"}
    progs = {
        "addz": lambda x: x + 0.0,
        "idx": lambda x: x,
        "subz": lambda x: x - 0.0,
        "mul2": lambda x: x * 2.0,
        "add2": lambda x: x + x,
        "sqsq": safe(lambda x: math.sqrt(x * x)),
        "absx": lambda x: abs(x),
        "xmx": lambda x: x - x,
        "zero": lambda x: 0.0,
    }
    for k in range(6):
        progs[f"c{k}"] = (lambda kk: (lambda x: x * (1.0 + kk * 4e-10)))(k)
    resolutions = [("r0", FLOAT_R0, False), ("r1", FLOAT_R1, False)]
    universe = FLOAT_U
    contexts = {"recip": lambda f: (lambda x: ieee_div(1.0, f(x)))}
    compositional = {("bits", "recip"): True, ("value", "recip"): False}

    def run(self, prog, inputs, sched, obs):
        tick(len(inputs))
        vals = [prog(x) for x in inputs]
        if obs == "bits":
            return tuple(bits(v) for v in vals)
        if obs == "value":
            return tuple(value(v) for v in vals)
        return tuple(vals)

    @staticmethod
    def related(obs, va, vb):
        return all(close(a, b) for a, b in zip(va, vb))


# ------------------------------------------------------------------- io

class IO:
    name = "I/O-bound (writes with short-write environment)"
    finite = False
    finest = None
    observers = {"content": "eq", "calls": "eq"}
    progs = {"w1": "one", "w2": "each", "w3": "swap", "w4": "loop", "w5": "loop2"}
    resolutions = [("r0", ["ab"], False), ("r1", ["a", "ab", "ba"], False)]
    universe = ["".join(p) for L in range(1, 4) for p in itertools.product("ab", repeat=L)]
    contexts = {}
    compositional = {}

    def exec(self, kind, s, shorts):
        # shorts: iterator of how many bytes each write call accepts
        content, calls = "", 0

        def write(buf):
            nonlocal content, calls
            calls += 1
            k = next(shorts, len(buf))
            k = max(1, min(k, len(buf)))
            content += buf[:k]
            return k

        if kind == "one":
            write(s)
        elif kind == "each":
            for ch in s:
                write(ch)
        elif kind == "swap":
            for ch in s:
                write({"a": "b", "b": "a"}[ch])
        elif kind == "loop":
            i = 0
            while i < len(s):
                i += write(s[i:])
        else:
            rest = s
            while rest:
                rest = rest[write(rest):]
        return content, calls

    def run(self, prog, inputs, sched, obs):
        out = []
        for s in inputs:
            pats = [()] if sched == "one" else list(itertools.product(range(1, len(s) + 1), repeat=len(s)))
            res = set()
            for pat in pats:
                c, n = self.exec(prog, s, iter(pat))
                res.add(c if obs == "content" else n)
                tick()
            out.append(tuple(sorted(res, key=repr)))
        return tuple(out)


# ------------------------------------------------------------------- ui

class UI:
    name = "UI components (event sequences, DOM)"
    finite = False
    finest = None
    observers = {"dom": "eq", "text": "eq", "handlers": "eq"}
    progs = {k: k for k in ("A", "A2", "B", "C", "D")}

    @staticmethod
    def seqs(n):
        return [s for L in range(n + 1) for s in itertools.product(("click", "key"), repeat=L)]

    resolutions = None
    universe = None
    contexts = {}
    compositional = {}

    def __init__(self):
        self.resolutions = [("r0", self.seqs(1), False), ("r1", self.seqs(3), False)]
        self.universe = self.seqs(5)

    def render(self, kind, n):
        if kind == "A2":
            label = "%d" % n
            return tuple(["div", tuple([tuple(["button", (label,)])])])
        tag = "span" if kind == "C" else "div"
        return (tag, (("button", (str(n),)),))

    def text(self, dom):
        tag, kids = dom
        return "".join(k[1][0] for k in kids)

    def run(self, prog, inputs, sched, obs):
        out = []
        for s in inputs:
            n, handled, clicks, trace = 0, 0, 0, []
            for ev in s:
                if ev == "click":
                    clicks += 1
                    n += 2 if (prog == "D" and clicks > 3) else 1
                    handled += 1
                elif prog == "B":
                    handled += 1
                dom = self.render(prog, n)
                trace.append(dom if obs == "dom" else self.text(dom))
            out.append(handled if obs == "handlers" else tuple(trace))
            tick()
        return tuple(out)


# ------------------------------------------------------------- compiler

def ev(e, x):
    op = e[0]
    if op == "c":
        return e[1]
    if op == "x":
        return x
    a, b = ev(e[1], x), ev(e[2], x)
    if op == "+":
        return a + b
    if op == "-":
        return a - b if not (math.isinf(a) and math.isinf(b) and a == b) else float("nan")
    if op == "*":
        try:
            return a * b
        except OverflowError:
            return math.copysign(math.inf, a) * math.copysign(1.0, b)
    return ieee_div(a, b)


def optimize(e, passes):
    if e[0] in ("c", "x"):
        return e
    a, b = optimize(e[1], passes), optimize(e[2], passes)
    op = e[0]
    if "fold" in passes and a[0] == "c" and b[0] == "c":
        return ("c", ev((op, a, b), 0.0))
    if "mul0" in passes and op == "*" and b == ("c", 0.0):
        return ("c", 0.0)
    if "subself" in passes and op == "-" and a == b:
        return ("c", 0.0)
    if "reassoc" in passes and op == "+" and a[0] == "+":
        return ("+", a[1], ("+", a[2], b))
    if "mul2" in passes and op == "*" and b == ("c", 2.0):
        return ("+", a, a)
    return (op, a, b)


def compile_stack(e):
    if e[0] == "c":
        return [("push", e[1])]
    if e[0] == "x":
        return [("load",)]
    return compile_stack(e[1]) + compile_stack(e[2]) + [(e[0],)]


def vm(code, x):
    st = []
    for ins in code:
        if ins[0] == "push":
            st.append(ins[1])
        elif ins[0] == "load":
            st.append(x)
        else:
            b, a = st.pop(), st.pop()
            st.append(ev((ins[0], ("c", a), ("c", b)), 0.0))
    return st[0]


SOURCES = {
    "s1": ("+", ("*", ("x",), ("c", 0.0)), ("c", 1.0)),
    "s2": ("*", ("-", ("x",), ("x",)), ("c", 3.0)),
    "s3": ("+", ("+", ("x",), ("c", 0.1)), ("c", 0.2)),
    "s4": ("+", ("*", ("x",), ("c", 2.0)), ("c", 1.0)),
}
PASSES = {"O0": (), "fold": ("fold",), "mul0": ("mul0",), "subself": ("subself",),
          "reassoc": ("reassoc", "fold"), "mul2": ("mul2",)}


class Compiler:
    name = "compilers (expression optimizer to stack VM)"
    finite = False
    finest = "bits"
    observers = {"bits": "eq", "value": "eq"}
    progs = {}
    for sname, src in SOURCES.items():
        progs[f"{sname}.src"] = (lambda e: (lambda x: ev(e, x)))(src)
        for pname, passes in PASSES.items():
            code = compile_stack(optimize(src, passes))
            progs[f"{sname}.{pname}"] = (lambda c: (lambda x: vm(c, x)))(code)
    resolutions = [("r0", FLOAT_R0, False), ("r1", FLOAT_R1, False)]
    universe = FLOAT_U
    contexts = {"recip": lambda f: (lambda x: ieee_div(1.0, f(x)))}
    compositional = {("bits", "recip"): True, ("value", "recip"): False}
    # Proof witnesses (Generalize.lean section 8). The Python passes
    # mirror the Lean definitions by reading, not by proof.
    proofs = []
    for sname in SOURCES:
        proofs.append((f"{sname}.src", f"{sname}.O0", "proof:compile_run"))
        proofs.append((f"{sname}.src", f"{sname}.fold", "proof:fold_sound+compile_run"))
        proofs.append((f"{sname}.src", f"{sname}.mul2",
                       "proof:rewrite_sound+compile_run;premise:ieee-doubling-exact"))

    def run(self, prog, inputs, sched, obs):
        tick(len(inputs))
        vals = [prog(x) for x in inputs]
        return tuple(bits(v) if obs == "bits" else value(v) for v in vals)


KINDS = [Pure(), Stateful(), Concurrent(), Distributed(), Float(), IO(), UI(), Compiler()]
