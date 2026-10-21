# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m54.py (jobs m54a, m54b). The full check (m52's kind-graph count, every
representative, the planted control solved) is --part check, which each job runs as its own
step."""
import unittest

import m52
import m53
import m54 as m
import sat_aniso as sa


class TestM54(unittest.TestCase):
    def test_perm(self):
        self.assertEqual(sorted(m.PERM), list(range(7)))
        self.assertEqual(sorted(m.bm(v) for v in range(128)), list(range(128)))
        self.assertEqual(m.bm(m52.X0), 1)
        self.assertEqual(m.bm((1 << 2) | (1 << 6)), 3)

    def test_frame(self):
        self.assertTrue(m.frame_moves())

    def test_au(self):
        self.assertEqual(m.AU, m.M42B_REP_O002)
        self.assertEqual(m.to_m42(m52.au_of("graph")), m.AU)
        self.assertEqual(m53.kernel(m.AU, 7), m.X1)
        self.assertEqual(m53.column_space(m.AU, 7), m.R)
        self.assertEqual(m53.dim_meet(m.X1, m.R), 3)
        self.assertEqual(m53.dim_meet(m.R, m53.p_basis(6)), 2)
        self.assertFalse(m53.in_span(m.R, 1))

    def test_ring_map(self):
        self.assertTrue(m.ring_map_check(60, 1))

    def test_admissible(self):
        e = sa.entries
        self.assertFalse(m.admissible(0))
        self.assertFalse(m.admissible(m.AU))
        self.assertTrue(m.admissible(e(7, [(2, 4)])))                               # rank 0 on X_1
        self.assertTrue(m.admissible(e(7, [(2, 1), (3, 2)])))                       # rank 2 on X_1
        self.assertFalse(m.admissible(e(7, [(2, 1), (3, 2), (0, 3), (1, 3)])))      # rank 3 on X_1
        self.assertFalse(m.admissible(e(7, [(2, 0)])))                              # A x0 != 0
        self.assertFalse(m.admissible(e(7, [(0, 5)])))                              # image not in R
        for rep_cols in ((0, 0, 0, 1, 0, 0, 0), (2, 0, 0, 0, 0, 0, 0), (0, 68, 1, 0, 0, 0, 0)):
            self.assertTrue(m.admissible(m.to_m42(rep_cols)))

    def test_batches(self):
        a, b = m.BATCHES["a"], m.BATCHES["b"]
        self.assertEqual((a[0], a[1], b[0], b[1]), (0, 89, 89, m.CLASSES))
        self.assertEqual(sum(m.HAND_G.values()), m.CLASSES)
        self.assertEqual(m52.HAND_ORBITS["graph"], {int(k): v for k, v in m.HAND_G.items()})

    def test_probe(self):
        rep = {"m42": sa.entries(7, [(2, 4)]), "rank_x1": 0, "index": 0, "size": 1}
        cnf, names, hints, units = m53.build(m.spec_of(0, rep))
        self.assertEqual(hints, m53.HAND_HINTS_B6)
        self.assertEqual(units, 49)
        self.assertTrue(m53.units_consistent(cnf))

    def test_m52_structure(self):
        s = m52.structure("graph")
        self.assertTrue(s["rank_au"] == 3 and s["ker_is_x1"] and s["r_in_x1"] and s["kind_ok"])


if __name__ == "__main__":
    unittest.main()
