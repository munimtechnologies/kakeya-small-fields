# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m42.py (job m42). The classification at t = 6 and t = 7 is in --part selfcheck,
which the job runs as its own step."""
import unittest

import m42 as m
import sat_aniso as sa


class TestM42(unittest.TestCase):
    def test_subspaces(self):
        self.assertEqual(len(m.subspaces(4, 2, 1)), 7)
        subs = m.subspaces(4, 2)
        self.assertEqual(len(subs), 35)
        self.assertTrue(all(m.rref(s) == s for s in subs))
        self.assertEqual(len(m.subspaces(5, 2)), 155)

    def test_generators(self):
        self.assertEqual(len(m.generators(7, 6)), 30)
        self.assertEqual(len(m.generators(7, 5)), 26)
        for p in (6, 5):
            self.assertTrue(all(m.in_group(g, 7, p) for g in m.generators(7, p)))
        # e_1 -> e_1 + e_0 leaves P, so it is not in G.
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << 1), 7, 6))

    def test_group_t4(self):
        self.assertEqual(len(m.group_elements(4, 3)), m.group_order(4, 3))
        self.assertEqual(len(m.group_elements(4, 2)), m.group_order(4, 2))
        self.assertEqual(m.group_order(7, 6), m.HAND_GROUP[(7, 6)])
        self.assertEqual(m.group_order(7, 5), m.HAND_GROUP[(7, 5)])

    def test_matrices(self):
        x1 = m.rref([1, 2, 4, 8])
        r = m.rref([16, 32, 64 | 1])
        mats = m.matrices(7, x1, r)
        self.assertEqual(len(mats), 168)
        self.assertTrue(all(m.kernel(A, 7) == x1 and m.column_space(A, 7) == r for A in mats))

    def test_units(self):
        x1 = m.rref([1, 2, 4, 8])
        units, st = m.random_units(7, [(1,), m.p_basis(6), x1], 8, 5)
        self.assertEqual(len(units), 8)
        self.assertEqual(st["algebra_dim"], 28)
        self.assertTrue(all(m.in_group(g, 7, 6, (x1,)) for g in units))

    def test_exact_t4(self):
        ex = m.exact_check(4, 3, 2)
        self.assertEqual(ex["pairs"], 7)
        self.assertEqual(ex["sizes"], m.HAND_T4_B3_SIZES)
        self.assertTrue(ex["pairs_exact"] and ex["H_orbit_stabiliser"] and ex["classes_exact"])
        ex = m.exact_check(4, 2, 2)
        self.assertEqual(ex["pairs"], 19)
        self.assertTrue(ex["pairs_exact"] and ex["H_orbit_stabiliser"] and ex["classes_exact"])
        self.assertEqual(m.exact_check(2, 1, 1)["pairs"], 3)

    def test_phis(self):
        self.assertEqual(m.phis_for(9, 6), (None, 0, 0, 2, 4, 8, 16, 32, 64))
        self.assertEqual(m.phis_for(9, 5), (None, 0, 0, 0, 2, 4, 8, 16, 32))
        self.assertEqual(m.phis_for(2, 1), (None, 2))

    def test_hints_t4(self):
        for p, n in ((3, m.HAND_HINTS["t4_B3"]), (2, m.HAND_HINTS["t4_B2"])):
            pr = m.pair_orbits(4, p, 2)[0][0]
            au = m.matrices(4, pr["x1"], pr["r"])[0]
            cnf, names, k = m.build({"name": "x", "kind": "control", "t": 4, "d": 5, "p": p,
                                     "au": au})
            self.assertEqual(k, n)
            self.assertTrue(m.units_consistent(cnf))

    def test_planted(self):
        As, ss, B = m.planted()
        at, sv = sa.tables(As, ss, B, 6)
        self.assertTrue(sa.is_system(at, sv, 6, 6))
        self.assertTrue(sa.anisotropic(sv))
        cnf, names, n = m.build(m.planted_spec())
        self.assertEqual(n, m.HAND_HINTS["planted"])
        self.assertTrue(sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, 6, 6)))


if __name__ == "__main__":
    unittest.main()
