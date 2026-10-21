# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m53.py (job m53). The full check (m52's kind-P count, every representative, the
planted control solved) is --part check, which the job runs as its own step."""
import unittest

import m52
import m53 as m
import sat_aniso as sa


class TestM53(unittest.TestCase):
    def test_shift(self):
        self.assertEqual(sorted(m.shift(v) for v in range(128)), list(range(128)))
        self.assertEqual(m.shift(1 << 6), 1)
        for k in range(6):
            self.assertEqual(m.shift(1 << k), 1 << (k + 1))

    def test_au(self):
        self.assertEqual(m.to_m42(m52.au_of("P")), m.AU)
        self.assertEqual(m.kernel(m.AU, 7), m.X1)
        self.assertEqual(m.column_space(m.AU, 7), m.R)
        self.assertEqual(m.dim_meet(m.X1, m.R), 3)
        self.assertFalse(m.in_span(m.R, 1))

    def test_ring_map(self):
        self.assertTrue(m.ring_map_check(60, 1))

    def test_admissible(self):
        e = sa.entries
        self.assertFalse(m.admissible(0))
        self.assertFalse(m.admissible(m.AU))
        self.assertTrue(m.admissible(e(7, [(1, 4)])))                       # rank 0 on X_1
        self.assertTrue(m.admissible(e(7, [(2, 1), (3, 2)])))               # rank 2 on X_1
        self.assertFalse(m.admissible(e(7, [(2, 1), (3, 2), (1, 3)])))      # rank 3 on X_1
        self.assertFalse(m.admissible(e(7, [(1, 0)])))                      # A x0 != 0
        self.assertFalse(m.admissible(e(7, [(0, 5)])))                      # image not in R
        for rep_cols in ((0, 0, 0, 1, 0, 0, 0), (2, 0, 0, 0, 0, 0, 0), (0, 4, 1, 0, 0, 0, 0)):
            self.assertTrue(m.admissible(m.to_m42(rep_cols)))

    def test_probe(self):
        rep = {"m42": sa.entries(7, [(1, 4)]), "rank_x1": 0, "index": 0, "size": 1}
        cnf, names, hints, units = m.build(m.spec_of(0, rep))
        self.assertEqual(hints, m.HAND_HINTS_B6)
        self.assertEqual(units, 49)
        self.assertTrue(m.units_consistent(cnf))

    def test_planted(self):
        As, ss, B = m.planted()
        pc, pn, _, _ = m.build(m.planted_with_a1())
        self.assertTrue(sa.satisfies(pc, sa.assignment(pc, pn, As, ss, B, 6, 6)))
        qc, qn, _, _ = m.build(m.planted_with_a1(As[1] ^ (1 << 7)))
        self.assertFalse(sa.satisfies(qc, sa.assignment(qc, qn, As, ss, B, 6, 6)))

    def test_m52_structure(self):
        s = m52.structure("P")
        self.assertTrue(s["rank_au"] == 3 and s["ker_is_x1"] and s["r_in_x1"] and s["kind_ok"])


if __name__ == "__main__":
    unittest.main()
