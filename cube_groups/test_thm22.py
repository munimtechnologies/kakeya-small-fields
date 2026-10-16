# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import thm22


class TestMatrices(unittest.TestCase):
    def test_identity_and_products(self):
        for A in range(16):
            self.assertEqual(thm22.mat_mul(thm22.IDENTITY, A), A)
            self.assertEqual(thm22.mat_mul(A, thm22.IDENTITY), A)
            for x in range(4):
                for B in range(16):
                    self.assertEqual(thm22.mat_apply(thm22.mat_mul(A, B), x),
                                     thm22.mat_apply(A, thm22.mat_apply(B, x)))
        self.assertEqual(len(thm22.m2_subspaces()), 67)

    def test_m2_table(self):
        self.assertEqual(thm22.m2_table(), thm22.M2_TABLE_PREDICTED)


class TestSolver(unittest.TestCase):
    def test_lemma15_example(self):
        # sigma = (x1 x2, 0) with alpha(h) = (x1 + x2) E_11: the rank-2 case of Lemma 15 inside X.
        m, tabs = 2, thm22.mon_tables(2)
        target = 1 << thm22.monomials(2).index((0, 1))
        sol = thm22.solve_sigma([1, 1], m)
        self.assertEqual(thm22.rank_f2(sol + [target]), thm22.rank_f2(sol))
        self.assertTrue(thm22.identity_holds(thm22.alpha_table([1, 1], m),
                                             thm22.sigma_from_coeffs(target, m, tabs), m))
        # With alpha = 0 the identity forces beta = 0, so x1 x2 is not a solution.
        sol0 = thm22.solve_sigma([0, 0], m)
        self.assertEqual(len(sol0), 2 * m)
        self.assertGreater(thm22.rank_f2(sol0 + [target]), thm22.rank_f2(sol0))

    def test_reduction_matches_full_identity(self):
        rng = random.Random(5)
        m = 4
        tabs = thm22.mon_tables(m)
        N = len(tabs)
        for _ in range(6):
            cols = [rng.getrandbits(4) for _ in range(m)]
            at = thm22.alpha_table(cols, m)
            sol = thm22.solve_sigma(cols, m)
            for c in sol:
                self.assertTrue(thm22.identity_holds(at, thm22.sigma_from_coeffs(c, m, tabs), m))
            while True:
                c = rng.getrandbits(2 * N)
                if thm22.rank_f2(sol + [c]) > thm22.rank_f2(sol):
                    break
            self.assertFalse(thm22.identity_holds(at, thm22.sigma_from_coeffs(c, m, tabs), m))

    def test_min_singular_codim(self):
        m = 2
        masks = {d: thm22.subspace_masks(m, d) for d in range(m + 1)}
        tabs = thm22.mon_tables(m)
        mons = thm22.monomials(m)
        aniso = sum(1 << mons.index(t) for t in [(0, 0), (1, 1), (0, 1)])  # x1 + x2 + x1 x2
        self.assertEqual(thm22.min_singular_codim(thm22.sigma_from_coeffs(aniso, m, tabs), m, masks), 2)
        lin = 1 << mons.index((0, 0))  # x1
        self.assertEqual(thm22.min_singular_codim(thm22.sigma_from_coeffs(lin, m, tabs), m, masks), 1)
        self.assertEqual(thm22.min_singular_codim((0, 0), m, masks), 0)


class TestLemma20(unittest.TestCase):
    def test_small_dimensions(self):
        st = thm22.lemma20_run(seed=3, m_list=(2, 3, 4), trials=1, cap=16, explore_m=4,
                               explore_cap=4, full_checks=1)
        self.assertTrue(st["match"], st["violations"])
        dims = {k.split(",")[1] for k in st["rank_alpha_dim_sigma_K"]}
        self.assertEqual(dims, {"0", "1", "2"})
        self.assertGreater(st["sigmas_spanning_X"], 0)


class TestCaseBounds(unittest.TestCase):
    def test_settled_table(self):
        for a in range(1, 9):
            for b in range(0, 9):
                self.assertEqual(thm22.case_bounds(a, b)["settled"], thm22.settled_predicted(a, b),
                                 (a, b))

    def test_named_cases(self):
        for a, b in [(5, 2), (4, 3), (4, 8), (3, 8), (8, 1)]:
            self.assertTrue(thm22.case_bounds(a, b)["settled"], (a, b))
        self.assertEqual(thm22.case_bounds(6, 2)["open"], [[3, d, 6, 19] for d in range(3, 7)])
        self.assertEqual(thm22.case_bounds(5, 3)["open"], [[3, d, 6, 20] for d in range(3, 6)])


if __name__ == "__main__":
    unittest.main()
