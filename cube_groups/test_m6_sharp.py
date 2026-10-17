# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m6_sharp as ms


def example1():
    # Example 1 of finite-groups.md: t = 3, V = F_2^2, A_1 = E_11, A_2 = E_12 + E_13 + E_21 + E_22
    # (1-based), sigma(e_1) = e_2 + e_3, sigma(e_2) = e_1 + e_2 + e_3, sigma(e_1 + e_2) = e_1 + e_2.
    A1 = ms.entries(3, [(0, 0)])
    A2 = ms.entries(3, [(0, 1), (0, 2), (1, 0), (1, 1)])
    return [0, A1, A2, A1 ^ A2], [0, 6, 7, 3]


class TestLemma30(unittest.TestCase):
    def test_example1(self):
        at, sv = example1()
        self.assertTrue(ms.is_system(at, sv, 2, 3))
        self.assertTrue(ms.anisotropic(sv))
        rhos = []
        for u in (1, 2, 3):
            r = ms.lemma30_check(at, sv, 2, 3, u)
            rhos.append(r["rho"])
            self.assertTrue(r["a"] and r["outside"])
            self.assertEqual((r["dim_plus"], r["codim_plus"], r["image"]), (1, 1, 1))
            self.assertFalse(r["x0_in_image"])
            self.assertTrue(all(ms.grade_aniso(r, 2, 3).values()))
        self.assertEqual(rhos, [1, 2, 2])

    def test_diagonal(self):
        m, at, sv = ms.diagonal(2)
        self.assertEqual(m, 4)
        self.assertTrue(ms.is_system(at, sv, 4, 2))
        self.assertTrue(all(ms.lemma30_check(at, sv, 4, 2, u)["a"] for u in range(16)))
        # span(h_1, h_2) with h_1 = (u = (1, 0), v = (0, 1)) = 9 and h_2 = (u = 0, v = (1, 0)) = 4
        k, at_w, sv_w = ms.restrict(at, sv, [9, 4])
        self.assertEqual((at_w, sv_w), ([0, 1, 0, 1], [0, 2, 1, 2]))
        self.assertTrue(ms.is_system(at_w, sv_w, k, 2) and ms.anisotropic(sv_w))
        got = []
        for u in (1, 2, 3):
            r = ms.lemma30_check(at_w, sv_w, k, 2, u)
            got.append((r["rho"], r["codim_plus"], r["x0_in_image"]))
            self.assertTrue(all(ms.grade_aniso(r, k, 2).values()))
        self.assertEqual(got, [(1, 1, False), (0, 0, True), (1, 1, False)])

    def test_not_a_system(self):
        # x^2 + xy + y^2 with alpha = 0 is no system, and (a) fails at u = e_1: phi(e_2) = 1 = x0
        # but A_(e_2) x0 = 0.
        at, sv = [0, 0, 0, 0], [0, 1, 1, 1]
        self.assertFalse(ms.is_system(at, sv, 2, 1))
        self.assertFalse(ms.lemma30_check(at, sv, 2, 1, 1)["a"])

    def test_random(self):
        rng = random.Random(7)
        cases = []
        for _ in range(10):
            B = ms.independent([rng.getrandbits(9) for _ in range(rng.randint(1, 3))])
            m, at = ms.system(B, rng.randint(0, 2))
            if m == 0:
                continue
            tabs = ms.mon_tables(m)
            sol = ms.solve_sigma(at, m, 3)
            for _ in range(2 if sol else 0):
                v = ms.combine(sol, rng.getrandbits(len(sol)))
                cases.append((m, at, ms.table(ms.sigma_from_coeffs(v, tabs, 3), m)))
        cases.append(ms.diagonal(3))
        self.assertGreater(len(cases), 3)
        for m, at, sv in cases:
            if m <= 5:
                self.assertTrue(all(ms.lemma30_check(at, sv, m, 3, u)["a"]
                                    for u in range(1 << m)))
            for _ in range(2):
                basis = ms.greedy_anisotropic(sv, m, rng)
                if not basis:
                    continue
                k, at_w, sv_w = ms.restrict(at, sv, basis)
                self.assertTrue(ms.is_system(at_w, sv_w, k, 3) and ms.anisotropic(sv_w))
                self.assertLessEqual(k, 3)
                for u in range(1, 1 << k):
                    r = ms.lemma30_check(at_w, sv_w, k, 3, u)
                    self.assertTrue(all(ms.grade_aniso(r, k, 3).values()))


class TestCases(unittest.TestCase):
    def test_bounds(self):
        A, E = ms.bounds(12)
        self.assertEqual(A, [0, 1, 2, 3, 4, 6, 8, 10, 12, 15, 18, 21, 24])
        self.assertEqual(E, [0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 8, 10, 12])

    def test_settled(self):
        out = ms.cases()
        self.assertTrue(all(out["graded"].values()))
        self.assertEqual({b: out["first_open"][str(b)] for b in range(2, 12)},
                         {2: 10, 3: 10, 4: 11, 5: 11, 6: 12, 7: 12, 8: 13, 9: 13, 10: 14, 11: 14})
        for a, b in ((9, 2), (9, 3), (9, 4), (10, 4), (10, 5), (10, 6), (11, 7), (13, 10)):
            self.assertTrue(ms.settled(a, b))
        for a, b in ((10, 2), (10, 3), (11, 4), (11, 5), (12, 6), (14, 10), (14, 11)):
            self.assertFalse(ms.settled(a, b))


if __name__ == "__main__":
    unittest.main()
