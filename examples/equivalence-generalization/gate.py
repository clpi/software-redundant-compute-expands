"""Gates for the equivalence-generalization fixes.

Each fix has a gate that fails without the fix and passes with it.
The policy without the fix is the "before"; v1 is the "after".
Exit 0 only if every gate holds.

Usage: python3 gate.py RESULTS.json
"""

import json
import sys

FALSE = ("false_bare", "false_qualified", "congruence_false", "tolerance_false")


def total(res, policy, fields=FALSE, kinds=None):
    ks = res[policy]["kinds"]
    return sum(ks[k][f] for k in ks if kinds is None or k in kinds for f in fields)


def main(path):
    res = json.load(open(path))
    gates = []

    def gate(name, before, after):
        ok = before > 0 and after == 0
        gates.append((name, before, after, ok))

    # v0 is the spec read literally: a bounded measurement witnesses a
    # join of two program terms. It must fail somewhere in every kind.
    for k, ev in res["v0"]["kinds"].items():
        gates.append((f"v0 fails on {k}", ev["false_bare"], None, ev["false_bare"] > 0))

    gate("observer-applied terms (leak across observers)",
         total(res, "v1-no-observer"), total(res, "v1"))
    gate("resolution in the head; bare join only when exhaustive",
         total(res, "v1-no-resolution"), total(res, "v1"))
    gate("schedule sets on nondeterministic kinds",
         total(res, "v0", fields=("schedule_false",)), total(res, "v0+schedules", fields=("schedule_false",)))
    gate("tolerance as a relation term, not a join",
         total(res, "v1-no-tolerance", fields=("tolerance_false",)), total(res, "v1", fields=("tolerance_false",)))
    gate("congruence only for compositional observers",
         total(res, "v1-no-congruence", fields=("congruence_false",)), total(res, "v1", fields=("congruence_false",)))

    # v1 and v1+proofs: no false fact of any kind, every graph valid.
    for p in ("v1", "v1+proofs"):
        bad = total(res, p)
        inval = sum(1 for ev in res[p]["kinds"].values() if not ev["valid"])
        gates.append((f"{p} sound and valid", bad + inval, None, bad == 0 and inval == 0))

    # proofs recover bare joins the measurement policy must refuse
    m1 = total(res, "v1", fields=("missed_bare",))
    m2 = total(res, "v1+proofs", fields=("missed_bare",))
    gates.append(("proof witnesses recover bare joins", m1 - m2, None, m2 < m1))

    ok = True
    for name, b, a, g in gates:
        ok &= g
        print(("PASS" if g else "FAIL"), name, f"before={b}", "" if a is None else f"after={a}")
    print("ALL PASS" if ok else "GATE FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1]))
