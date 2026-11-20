from itertools import combinations
from random import Random
import unittest
from action_support import Edge, Supports, choose, frontier, oracle, try_stop


class Experiment(unittest.TestCase):
    def test_complement_and_reweight(self):
        e = (Edge(("reading","selected"),"done"),
             Edge(("combined",),"done"),
             Edge(("done",),"metric"))
        ws = (("reading","read"),("selected","select"),("combined","both"))
        s = Supports()
        s.append(e, ws[:1])
        self.assertEqual(s.require_all(("metric",)), ())
        s.append(witnesses=ws[1:2])
        self.assertEqual(s.require_all(("metric",)), (frozenset(("read","select")),))
        s.append(witnesses=ws[2:])
        plans = s.require_all(("done","metric"))
        f = frontier(plans, lambda p:(9,1) if "both" in p else (4,2))
        evaluations = s.evaluations
        self.assertEqual(choose(f,(1,1))[0],frozenset(("read","select")))
        self.assertEqual(choose(f,(1,10))[0],frozenset(("both",)))
        self.assertEqual(s.evaluations,evaluations)
        self.assertFalse(try_stop(True,(4,2),[(1,20)]))
        self.assertTrue(try_stop(True,(4,2),[(5,3),(4,4)]))

    def test_random_against_independent_oracle(self):
        for index in range(64):
            rng = Random(index)
            symbols = list("abcdef")
            witness = [(rng.choice(symbols),str(i)) for i in range(6)]
            edges = [Edge(tuple(rng.sample(symbols,rng.randrange(4))),rng.choice(symbols))
                    for _ in range(12)]
            incremental = Supports()
            goals = ("e","f")
            for k in range(1,5):
                with self.subTest(seed=index,prefix=k):
                    incremental.append(edges[3*(k-1):3*k],witness[2*(k-1):2*k])
                    expected = oracle(edges[:3*k],witness[:2*k],goals)
                    self.assertEqual(set(incremental.require_all(goals)),expected)
                    cold = Supports()
                    cold.append(edges[:3*k],witness[:2*k])
                    self.assertEqual(cold.require_all(goals),incremental.require_all(goals))


if __name__ == "__main__":
    unittest.main()
