# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import case33


class TestHelpers(unittest.TestCase):
    def test_subspaces_once_each(self):
        for n, c in [(4, 0), (4, 1), (4, 2), (4, 3), (5, 2), (6, 3)]:
            spans = set()
            for rows in case33.subspaces(n, c):
                self.assertEqual(case33.rank_f2(rows), c)
                span = {0}
                for r in rows:
                    span |= {x ^ r for x in span}
                spans.add(frozenset(span))
            self.assertEqual(len(spans), case33.gaussian_binomial(n, c))
            self.assertEqual(sum(1 for _ in case33.subspaces(n, c)), len(spans))
        self.assertEqual(case33.gaussian_binomial(4, 2), 35)
        self.assertEqual(case33.gaussian_binomial(9, 2), 43435)

    def test_kernel_of_w(self):
        for a, b in [(2, 2), (3, 2), (2, 3)]:
            for w in range(1, 1 << a):
                basis = case33.kernel_of_w(w, a, b)
                self.assertEqual(len(basis), a * b - b)
                self.assertTrue(all(case33.apply(M, w, a, b) == 0 for M in basis))


class TestProposition19(unittest.TestCase):
    def test_b2_matches_proposition_18(self):
        for c in (0, 1):
            r = case33.prop19_report(2, 2, c)
            self.assertEqual(r["kernel_zero"], r["spaces"])
            self.assertEqual(r["lam_zero"], r["spaces"])
        r = case33.prop19_report(2, 2, 1)
        self.assertEqual(r["spaces"], 15)
        self.assertEqual(r["special"], 9)               # C^perp with C of rank 1
        self.assertEqual(r["special_polar_nonzero"], 9)
        self.assertEqual(r["nonspecial_polar_nonzero"], 0)

    def test_b3(self):
        for a in (1, 2):
            for c in (0, 1, 2):
                r = case33.prop19_report(a, 3, c)
                self.assertEqual(r["spaces"], case33.gaussian_binomial(3 * a, c))
                self.assertEqual(r["lam_zero"], r["spaces"])
        r = case33.prop19_report(2, 3, 2)
        self.assertEqual(r["special"], 21)
        self.assertEqual(r["special_polar_nonzero"], 21)

    def test_control_codim_b(self):
        for a, b in [(1, 2), (2, 2), (2, 3)]:
            r = case33.prop19_report(a, b, b)
            self.assertEqual(r["kernel_nonzero"], (1 << a) - 1)

    def test_polar_solution_on_special_space(self):
        # W = {M : M w in span(u)} in Hom(F_2^2, F_2^3), lam(M) = (y^T M w) w with y^T u = 1
        a, b, w, u, y = 2, 3, 0b01, 0b001, 0b001
        W = [M for M in range(1 << (a * b)) if case33.apply(M, w, a, b) in (0, u)]
        self.assertEqual(len(W), 1 << (a * b - b + 1))

        def lam(M):
            return w if case33.parity(y & case33.apply(M, w, a, b)) else 0
        polar = all(case33.apply(M, lam(M2), a, b) == case33.apply(M2, lam(M), a, b)
                    for M in W for M2 in W)
        diagonal = all(case33.apply(M, lam(M), a, b) == 0 for M in W)
        self.assertTrue(polar)
        self.assertFalse(diagonal)


class TestLemma17(unittest.TestCase):
    def test_core(self):
        for a, b in [(1, 1), (1, 2), (2, 2), (2, 1), (3, 1), (3, 2)]:
            self.assertEqual(case33.lemma17_core(a, b), case33.lemma17_predicted(a, b))
        self.assertEqual(case33.lemma17_predicted(3, 2), 42)
        self.assertEqual(case33.lemma17_predicted(2, 2), 0)


class TestCaseBounds(unittest.TestCase):
    def test_settled(self):
        r = case33.case_bounds(3, 3)
        self.assertTrue(r["settled"])
        self.assertEqual(r["max_bound"], 15)
        self.assertFalse(case33.case_bounds(3, 3, new=False)["settled"])
        for a, b in [(1, 2), (2, 2), (2, 3), (2, 5), (3, 2), (4, 2)]:
            self.assertTrue(case33.case_bounds(a, b)["settled"])
        for a, b in [(1, 2), (2, 2), (2, 3), (3, 2), (4, 2)]:
            self.assertTrue(case33.case_bounds(a, b, new=False)["settled"])

    def test_open(self):
        for a, b in [(5, 2), (4, 3), (3, 4)]:
            self.assertFalse(case33.case_bounds(a, b)["settled"])
        self.assertIn([0, 2, 8, 17], case33.case_bounds(5, 2)["open"])


if __name__ == "__main__":
    unittest.main()
