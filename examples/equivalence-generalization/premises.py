"""Check, on the truth universe, the value-type laws the proof
witnesses rest on. This is a measurement, not a proof: it can refute
a law (one counterexample), never establish it.

Usage: python3 premises.py
"""

import math
import struct

from kinds import FLOAT_U


def b(v):
    return struct.pack(">d", v).hex()


def main():
    laws = {
        # rewrite e*2 -> e+e (mul2 pass): the premise the proof uses
        "doubling exact: u*2.0 == u+u (bits)": lambda u: b(u * 2.0) == b(u + u),
        # rewrite e*0 -> 0 (mul0 pass): no proof is admitted, here is why
        "zero absorbs: u*0.0 == 0.0 (bits)": lambda u: b(u * 0.0) == b(0.0),
        # rewrite e-e -> 0 (subself pass)
        "self-subtraction: u-u == 0.0 (bits)": lambda u: b(u - u if not math.isinf(u) else float("nan")) == b(0.0),
    }
    for name, law in laws.items():
        bad = [u for u in FLOAT_U if not law(u)]
        print(("HOLDS ON U" if not bad else "REFUTED"), name, "counterexamples:", bad[:4])


if __name__ == "__main__":
    main()
