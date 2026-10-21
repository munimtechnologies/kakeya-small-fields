# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m43.py (job m43). The classification at t = 6 and t = 7 and the hand counts of
Lemma 84 are in --part selfcheck, which the job runs as its own step."""
import unittest

import m43 as m
import sat_aniso as sa


class TestM43(unittest.TestCase):
    def test_group_order(self):
        for t, n in m.HAND_K.items():
            self.assertEqual(m.group_order(t), n)
        self.assertEqual(len(m.group_elements(4)), 4)
        self.assertEqual(len(m.group_elements(5)), 96)

    def test_generators(self):
        self.assertEqual(len(m.generators(7)), 20)
        self.assertEqual(len(m.generators(5)), 6)
        self.assertTrue(all(m.in_group(g, 7) for g in m.generators(7)))
        # e_1 -> e_1 + e_3 moves e_1, and e_3 -> e_3 + e_0 leaves P: neither is in K.
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << (7 * 3 + 1)), 7))
        self.assertFalse(m.in_group(m.identity(7) ^ (1 << (7 * 0 + 3)), 7))

    def test_subspaces(self):
        self.assertEqual(len(m.subspaces(7, 4, 4)), 1395)
        self.assertEqual(len(m.subspaces(7, 4, 5)), 1395)
        self.assertEqual(len(m.subspaces(6, 3, 5)), 155)
        self.assertEqual(len(m.subspaces(5, 2, 4)), 15)

    def test_r_orbit_totals(self):
        for t in (5, 6, 7):
            for form in m.FORMS:
                orbs = m.r_orbits(t, form)
                self.assertEqual(sum(s for _, s in orbs), m.HAND_R[t])
                self.assertTrue(all(m.group_order(t) % s == 0 for _, s in orbs))
                self.assertTrue(all(m.in_span(r, m.FORMS[form]) for r, _ in orbs))

    def test_matrices(self):
        r = m.rref([4, 8, 16, 32 | 64])
        mats = m.matrices(7, r)
        self.assertEqual(len(mats), 20160)
        self.assertTrue(all(A[:3] == (0, 0, 0) and m.rref(list(A)) == r for A in mats[:500]))
        self.assertEqual(len(m.matrices(6, m.rref([4, 8, 16]))), 168)
        self.assertEqual(len(m.matrices(5, m.rref([4, 8]))), 6)

    def test_conj(self):
        t = 7
        g = m.generators(t)[5]
        A = m.matrices(t, m.rref([4, 8, 16, 32 | 64]))[123]
        want = sa.mat_mul(sa.mat_mul(g, sa.from_cols(list(A), t), t), sa.mat_inv(g, t), t)
        self.assertEqual(m.conj(m.unit_pair(g, t), A), tuple(m.cols_of(want, t)))
        one = m.identity(t)
        self.assertEqual(m.conj(m.unit_pair(one, t), A), A)

    def test_units(self):
        r = m.rref([4, 8, 16, 32 | 64])
        units, st = m.random_units(7, [(1,), (2,), (4,), m.p_basis(6), r], 8, 5)
        self.assertEqual(len(units), 8)
        self.assertTrue(all(m.in_group(g, 7, (r,)) for g in units))

    def test_exact_t5(self):
        for form in m.FORMS:
            ex = m.exact_check(5, form)
            self.assertEqual(ex["group"], 96)
            self.assertTrue(ex["stabilisers"] and ex["classes_exact"])

    def test_encoding_t5(self):
        e = m.classify(5, "d2c1")[0]
        info = m.hint_info(5, "d2c1", e)
        self.assertEqual(info["hints"], m.HAND_HINTS[5])
        self.assertEqual(info["units"], m.AU_UNITS[5])
        self.assertTrue(info["consistent"])


if __name__ == "__main__":
    unittest.main()
