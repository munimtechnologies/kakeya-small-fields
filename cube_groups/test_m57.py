# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m57.py (job m57). The hand counts (d of each class, hint counts) are graded in
--part check, so a wrong hand number is a graded failure, not a crashed job."""
import unittest

import m57 as m
import sat_aniso as sa


class TestM57(unittest.TestCase):
    def test_lists(self):
        self.assertEqual(len(m.BATCH_C), 17)
        self.assertEqual(len(m.LEFTOVERS), 21)
        self.assertFalse(set(m.BATCH_C) & set(m.LEFTOVERS))
        self.assertNotIn("r3b_t7_B5_o027_c001", m.LEFTOVERS)
        for name in list(m.BATCH_C) + list(m.LEFTOVERS):
            pi, ci = m.pair_cls(name)
            self.assertEqual(name, f"r3b_t7_B5_o{pi:03d}_c{ci:03d}")
            self.assertIn(pi, m.PAIR_R)

    def test_plan(self):
        a, b = m.plan("a"), m.plan("b")
        self.assertEqual(len(a), 17)
        self.assertTrue(all(arm == "cadical" and cap == 900.0 for _, arm, cap, _ in a))
        self.assertEqual(len(b), 23)
        self.assertEqual([(s["name"], arm) for s, arm, _, _ in b[:2]],
                         [(m.A07["name"], "cadical"), (m.A07["name"], "xor")])
        self.assertEqual(b[1][3], "a07_open")
        self.assertTrue(all(arm == "xor" and cap == 300.0 for _, arm, cap, _ in b[2:]))

    def test_spec(self):
        sp = m.b5_spec("r3b_t7_B5_o048_c003", m.BATCH_C["r3b_t7_B5_o048_c003"])
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["kind"]), (7, 9, 5, "main"))
        self.assertEqual(sp["x1"], [64, 4, 2, 1])
        self.assertEqual(sp["r"], [72, 32, 17])
        t, d, au, s0, phis, kd, pvecs = m.params(sp)
        self.assertEqual((au, s0, kd), (36288195461136, 1, 4))

    def test_a07(self):
        self.assertEqual(m.B6_AU, 134744064)
        self.assertEqual(m.A07["a1"], 2048)
        self.assertEqual(m.column(m.A07["a1"], 4), 2)       # e_4 -> e_1
        self.assertEqual(sa.mat_mul(m.B6_AU, m.B6_AU, 7), 0)

    def test_xor_eq(self):
        c = m.XorCNF()
        x, y, z = c.new(), c.new(), c.new()
        c.xor_eq([x, -y, z, x], 1)          # x cancels; -y flips the right-hand side
        self.assertEqual(c.xors, [([y, z], 0)])
        c.xor_eq([x], 1)
        self.assertEqual(c.clauses[-1], [x])
        self.assertTrue(m.accepts(c, [None, True, True, True]))
        self.assertFalse(m.accepts(c, [None, True, True, False]))

    def test_with_xor_restores(self):
        cnf, _ = m.with_xor(sa.encode, 2, 2, True, True, False)
        self.assertIsInstance(cnf, m.XorCNF)
        self.assertIs(sa.CNF, m.sa.CNF)
        self.assertNotIsInstance(sa.encode(2, 2, echelon=False)[0], m.XorCNF)


if __name__ == "__main__":
    unittest.main()
