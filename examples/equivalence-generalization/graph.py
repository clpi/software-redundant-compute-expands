"""The one equivalence graph, as the spec defines it, in executable form.

Terms are nested tuples: an atom is ("atom", sym); a form is
("form", head, (arg, ...)). Edges are equivalence classes kept by a
union-find. The log is append only. There is no split operation, as
in the spec (section 8.2): edges only merge.
"""


def atom(s):
    return ("atom", s)


def form(head, *args):
    return ("form", head, tuple(args))


def applied(observer, *args):
    """The observer-applied term o(args...): a form whose head is the
    observer atom. This is the fix: measured facts join these terms,
    never the bare program terms."""
    return form(atom(observer), *args)


class Graph:
    def __init__(self):
        self.parent = {}
        self.log = []          # (kind, terms, level, witness)
        self.colors = {}       # root -> set of colors

    def _find(self, t):
        self.parent.setdefault(t, t)
        while self.parent[t] != t:
            self.parent[t] = self.parent[self.parent[t]]
            t = self.parent[t]
        return t

    def admit(self, t, level="", witness=""):
        self._find(t)
        self.log.append(("admit", (t,), level, witness))

    def join(self, a, b, level, witness):
        assert witness, "a join needs a witness"
        ra, rb = self._find(a), self._find(b)
        if ra != rb:
            self.parent[rb] = ra
            self.colors[ra] = self.colors.get(ra, set()) | self.colors.pop(rb, set())
        self.log.append(("join", (a, b), level, witness))

    def paint(self, t, color):
        r = self._find(t)
        self.colors.setdefault(r, set()).add(color)
        self.log.append(("paint", (t,), "", color))

    def same(self, a, b):
        if a not in self.parent or b not in self.parent:
            return a == b
        return self._find(a) == self._find(b)

    def edges(self):
        out = {}
        for t in list(self.parent):
            out.setdefault(self._find(t), []).append(t)
        return list(out.values())

    def valid(self):
        """Spec invariants 1 to 3 and 6: nonempty, duplicate free,
        disjoint edges that are exactly the classes the log's joins
        generate."""
        edges = self.edges()
        seen = set()
        for e in edges:
            if not e or len(set(e)) != len(e) or seen & set(e):
                return False
            seen |= set(e)
        # exactness: replay joins from scratch
        g = Graph()
        for kind, terms, level, witness in self.log:
            if kind == "admit":
                g._find(terms[0])
            elif kind == "join":
                g.parent.setdefault(terms[0], terms[0])
                g.parent.setdefault(terms[1], terms[1])
                ra, rb = g._find(terms[0]), g._find(terms[1])
                if ra != rb:
                    g.parent[rb] = ra
        mine = sorted(sorted(map(repr, e)) for e in edges)
        theirs = sorted(sorted(map(repr, e)) for e in g.edges())
        return mine == theirs
