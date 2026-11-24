"""Measure the one equivalence graph across eight kinds of software.

Policies are five independent flags:

  observer    measured facts join observer-applied terms o(p), not p
  resolution  the resolution and schedule set are part of the head;
              a bare join p = q needs an exhaustive resolution
  schedules   nondeterministic kinds are measured over every schedule
  tolerance   a tolerance relation is recorded as a relation term
              near(p, q) joined to `true`, never as a join of p and q
  congruence  a join is carried into a context C[p] = C[q] only for
              observers declared compositional for that context

v0 has every flag off: the spec read literally, with a bounded
measurement as the witness for a join of two program terms. v1 has
every flag on. The ablations turn one flag off at a time.

Usage: python3 measure.py OUT.json
"""

import itertools
import json
import sys

import kinds as K
from graph import Graph, atom, form

FLAGS = ("observer", "resolution", "schedules", "tolerance", "congruence")


def policies():
    out = {"v0": {f: False for f in FLAGS}, "v1": {f: True for f in FLAGS},
           "v1+proofs": dict({f: True for f in FLAGS}, proofs=True),
           "v0+schedules": dict({f: False for f in FLAGS}, schedules=True)}
    for f in FLAGS:
        p = {g: True for g in FLAGS}
        p[f] = False
        out[f"v1-no-{f}"] = p
    return out


NONDET = {"Concurrent", "Distributed", "IO"}


def prog_term(name):
    return atom(name)


def head(obs, res, pol):
    parts = []
    if pol["observer"]:
        parts.append(obs)
    if pol["resolution"]:
        parts.append(res)
    return "|".join(parts) if parts else None


def qterm(h, name):
    return prog_term(name) if h is None else form(atom(h), prog_term(name))


class Run:
    def __init__(self, kind, pol):
        self.k, self.pol = kind, pol
        self.kname = type(kind).__name__
        self.nondet = self.kname in NONDET
        self.progs = dict(kind.progs)
        self.ctx = {}
        for c in kind.contexts:
            for p in getattr(kind, "context_domain", kind.progs):
                if hasattr(kind, "wrap"):
                    self.ctx[f"{c}[{p}]"] = kind.wrap(c, kind.progs[p])
                else:
                    self.ctx[f"{c}[{p}]"] = kind.contexts[c](kind.progs[p])
        self.allp = dict(self.progs, **self.ctx)
        self.eqobs = [o for o, t in kind.observers.items() if t == "eq"]
        self.res = {name: (inputs, ex) for name, inputs, ex in kind.resolutions}
        self.g = Graph()
        self.cache = {}
        self.sep = {}           # (o, p, q) -> first resolution index that separated
        self.agreed = set()     # (o, p, q) agreed at some measured resolution
        self.bare_joins = []    # (p, q, resolution index)

    def observe(self, o, p, inputs_key, inputs, sched, count=True):
        key = (o, p, inputs_key, sched)
        if key not in self.cache:
            before = K.RUNS[0]
            self.cache[key] = self.k.run(self.allp[p], inputs, sched, o)
            if not count:
                K.RUNS[0] = before
        return self.cache[key]

    def related(self, o, va, vb):
        if self.k.observers[o] == "tol":
            return self.k.related(o, va, vb)
        return va == vb

    def measure(self):
        pol, k = self.pol, self.k
        sched = "all" if pol["schedules"] else "one"
        sched_exhaustive = (not self.nondet) or sched == "all"
        names = list(self.progs)
        for ri, (rname, inputs, exhaustive) in enumerate(k.resolutions):
            rhead = f"{rname}/{sched}"
            agree_all = {}
            for o, typ in k.observers.items():
                for p, q in itertools.combinations(names, 2):
                    va = self.observe(o, p, rname, inputs, sched)
                    vb = self.observe(o, q, rname, inputs, sched)
                    if not self.related(o, va, vb):
                        self.sep.setdefault((o, p, q), ri)
                        continue
                    self.agreed.add((o, p, q))
                    if typ == "eq":
                        agree_all.setdefault((p, q), set()).add(o)
                    wit = f"measure:{o}:{rhead}"
                    if typ == "tol" and pol["tolerance"]:
                        rel = form(atom("near"), atom(o), atom(rhead), prog_term(p), prog_term(q))
                        self.g.join(rel, atom("true"), rname, wit)
                        continue
                    h = head(o, rhead, pol)
                    if h is None:
                        self.g.join(prog_term(p), prog_term(q), rname, wit)
                        self.bare_joins.append((p, q, ri))
                    else:
                        self.g.join(qterm(h, p), qterm(h, q), rname, wit)
                        # promotion to a bare join
                        promote = False
                        if pol["observer"] and pol["resolution"]:
                            promote = (exhaustive and sched_exhaustive and typ == "eq"
                                       and agree_all.get((p, q), set()) >= set(self.eqobs))
                        elif pol["observer"]:
                            promote = typ == "eq" and agree_all.get((p, q), set()) >= set(self.eqobs)
                        elif pol["resolution"]:
                            promote = exhaustive and sched_exhaustive
                        if promote:
                            self.g.join(prog_term(p), prog_term(q), rname, f"promote:{rhead}")
                            self.bare_joins.append((p, q, ri))
        if pol.get("proofs"):
            for p, q, wit in getattr(k, "proofs", []):
                self.g.join(prog_term(p), prog_term(q), "", wit)
                self.proof_joins = getattr(self, "proof_joins", 0) + 1
        self.congruence()

    def congruence(self):
        pol, k = self.pol, self.k
        names = list(getattr(k, "context_domain", self.progs))
        for c in k.contexts:
            comp = {o: k.compositional.get((o, c), False) for o in k.observers}
            for p, q in itertools.combinations(names, 2):
                cp, cq = f"{c}[{p}]", f"{c}[{q}]"
                if self.g.same(prog_term(p), prog_term(q)):
                    # a bare join is equality under the finest observer,
                    # so it carries into a context exactly when the
                    # finest observer is compositional for it
                    fin = getattr(k, "finest", None)
                    if not pol["congruence"] or (fin is not None and comp.get(fin, False)):
                        self.g.join(prog_term(cp), prog_term(cq), "", f"congruence:{c}")
                for t in list(self.g.parent):
                    if t[0] != "form" or t[1][0] != "atom" or t[2] != (prog_term(p),):
                        continue
                    h = t[1][1]
                    if h in ("near",):
                        continue
                    o = h.split("|")[0] if pol["observer"] else None
                    if self.g.same(t, qterm(h, q)):
                        ok = (not pol["congruence"]) or (o is not None and comp.get(o, False))
                        if ok:
                            self.g.join(qterm(h, cp), qterm(h, cq), "", f"congruence:{c}")

    # ------------------------------------------------------------ truth

    def truth_bare(self, p, q):
        U = self.k.universe
        return all(self.observe(o, p, "U", U, "all", count=False) == self.observe(o, q, "U", U, "all", count=False)
                   for o in self.eqobs)

    def truth_head(self, h, p, q):
        pol = self.pol
        parts = h.split("|")
        o = parts[0] if pol["observer"] else None
        rh = parts[-1] if pol["resolution"] else None
        if rh:
            rname, sched = rh.split("/")
            inputs = self.res[rname][0]
            ikey = rname
        else:
            inputs, sched, ikey = self.k.universe, "all", "U"
        obs = [o] if o else self.eqobs
        for ob in obs:
            va = self.observe(ob, p, ikey, inputs, sched, count=False)
            vb = self.observe(ob, q, ikey, inputs, sched, count=False)
            if not self.related(ob, va, vb):
                return False
        return True

    def schedule_caused(self, p, q):
        """The pair agrees under one schedule but not under all, at a
        measured resolution, for some observer."""
        for rname, inputs, _ in self.k.resolutions:
            for o in self.eqobs:
                one = (self.observe(o, p, rname, inputs, "one", count=False)
                       == self.observe(o, q, rname, inputs, "one", count=False))
                alls = (self.observe(o, p, rname, inputs, "all", count=False)
                        == self.observe(o, q, rname, inputs, "all", count=False))
                if one and not alls:
                    return True
        return False

    def evaluate(self):
        r = {"schedule_false": 0, "false_bare": 0, "false_qualified": 0, "leak": 0, "congruence_false": 0,
             "tolerance_false": 0, "refuted_unsplit": 0, "missed_bare": 0,
             "true_bare": 0, "bare_pairs": 0, "qualified_pairs": 0, "relation_facts": 0,
             "valid": self.g.valid(), "examples": []}
        tol = {o for o, t in self.k.observers.items() if t == "tol"}
        for edge in self.g.edges():
            if atom("true") in edge:
                for t in edge:
                    if t == atom("true"):
                        continue
                    r["relation_facts"] += 1
                    _, o, rh, p, q = t[2][0][1], t[2][0], t[2][1][1], t[2][2][1], t[2][3][1]
                    rname, sched = rh.split("/")
                    va = self.observe(o[1], p, rname, self.res[rname][0], sched, count=False)
                    vb = self.observe(o[1], q, rname, self.res[rname][0], sched, count=False)
                    if not self.related(o[1], va, vb):
                        r["tolerance_false"] += 1
                continue
            groups = {}
            for t in edge:
                if t[0] == "atom":
                    groups.setdefault(None, []).append(t[1])
                else:
                    groups.setdefault(t[1][1], []).append(t[2][0][1])
            for h, members in groups.items():
                for p, q in itertools.combinations(sorted(members), 2):
                    isctx = "[" in p
                    if h is None:
                        r["bare_pairs"] += 1
                        ok = self.truth_bare(p, q)
                        if ok:
                            r["true_bare"] += 1
                            continue
                        r["false_bare"] += 1
                        if not isctx and self.nondet and self.schedule_caused(p, q):
                            r["schedule_false"] += 1
                        if isctx:
                            r["congruence_false"] += 1
                        else:
                            a, b = sorted((p, q))
                            if not any((o, a, b) in self.agreed or (o, b, a) in self.agreed for o in self.k.observers):
                                r["leak"] += 1
                            if any(o in tol and ((o, a, b) in self.agreed or (o, b, a) in self.agreed) for o in tol) \
                                    and not any(((o, a, b) in self.agreed or (o, b, a) in self.agreed) for o in self.eqobs):
                                r["tolerance_false"] += 1
                        if len(r["examples"]) < 4:
                            r["examples"].append(f"bare {p} = {q}")
                    else:
                        r["qualified_pairs"] += 1
                        if not self.truth_head(h, p, q):
                            r["false_qualified"] += 1
                            if isctx:
                                r["congruence_false"] += 1
                            elif self.pol["observer"] and h.split("|")[0] in tol:
                                r["tolerance_false"] += 1
                            if len(r["examples"]) < 4:
                                r["examples"].append(f"{h}: {p} = {q}")
        for p, q, ri in self.bare_joins:
            a, b = sorted((p, q))
            later = [self.sep.get((o, a, b), self.sep.get((o, b, a))) for o in self.eqobs]
            if any(s is not None and s > ri for s in later):
                r["refuted_unsplit"] += 1
        for p, q in itertools.combinations(list(self.progs), 2):
            if self.truth_bare(p, q) and not self.g.same(prog_term(p), prog_term(q)):
                r["missed_bare"] += 1
        r["truly_equal_base_pairs"] = sum(1 for p, q in itertools.combinations(list(self.progs), 2) if self.truth_bare(p, q))
        r["joins_logged"] = sum(1 for e in self.g.log if e[0] == "join")
        return r


def main(out):
    results = {}
    for pname, pol in policies().items():
        results[pname] = {"flags": pol, "kinds": {}}
        for kind in K.KINDS:
            K.RUNS[0] = 0
            run = Run(kind, pol)
            run.measure()
            runs = K.RUNS[0]
            ev = run.evaluate()
            ev["runs"] = runs
            ev["name"] = kind.name
            results[pname]["kinds"][type(kind).__name__] = ev
    with open(out, "w") as f:
        json.dump(results, f, indent=1, sort_keys=True)
    cols = ("false_bare", "leak", "refuted_unsplit", "congruence_false", "tolerance_false",
            "false_qualified", "missed_bare", "true_bare", "runs", "valid")
    for pname in results:
        print(f"== {pname}")
        print("kind".ljust(12) + "".join(c[:11].rjust(12) for c in cols))
        for kn, ev in results[pname]["kinds"].items():
            print(kn.ljust(12) + "".join(str(ev[c]).rjust(12) for c in cols))


if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "results.json")
