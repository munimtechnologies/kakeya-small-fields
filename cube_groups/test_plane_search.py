# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import plane_search as ps


def brute_max_singular_dim(S, m):
    """Largest dim of a subspace on which sigma vanishes, by listing every subspace."""
    nz = 0
    for q in S:
        nz |= q
    for d in range(m, -1, -1):
        for B in ps.subspaces(m, d):
            if all(not (nz >> x) & 1 for x in ps.span(B)):
                return d
    return 0


class TestMatrices(unittest.TestCase):
    def test_products_t3(self):
        rng = random.Random(1)
        one = ps.identity(3)
        for _ in range(200):
            A, B = rng.getrandbits(9), rng.getrandbits(9)
            self.assertEqual(ps.mat_mul(one, A, 3), A)
            self.assertEqual(ps.mat_mul(A, one, 3), A)
            for x in range(8):
                self.assertEqual(ps.mat_apply(ps.mat_mul(A, B, 3), x, 3),
                                 ps.mat_apply(A, ps.mat_apply(B, x, 3), 3))

    def test_structured_dimensions(self):
        dims = {k: len(v) for k, v in ps.structured_3().items()}
        self.assertEqual(dims["End"], 9)
        self.assertEqual(dims["trace0"], 8)
        self.assertEqual(dims["fix_line"], 7)
        self.assertEqual(dims["upper"], 6)
        self.assertEqual(dims["symmetric"], 6)
        self.assertEqual(dims["five"], 5)
        self.assertEqual(dims["F8"], 3)
        self.assertEqual(dims["jordan"], 3)

    def test_f8_is_a_field(self):
        # span(I, w, w^2) for the companion matrix of x^3 + x + 1: every non-zero element invertible.
        B = ps.structured_3()["F8"]
        for A in ps.span(B)[1:]:
            self.assertEqual(len({ps.mat_apply(A, x, 3) for x in range(8)}), 8)


class TestSingularSearch(unittest.TestCase):
    def test_against_brute_force(self):
        rng = random.Random(2)
        for m in (2, 3, 4, 5):
            tabs = ps.mon_tables(m)
            N = len(tabs)
            for t in (1, 2):
                for _ in range(12):
                    # sparse coefficients give large zero sets, dense ones small zero sets
                    c = rng.getrandbits(t * N) & rng.getrandbits(t * N)
                    S = ps.sigma_from_coeffs(c, tabs, t)
                    got, exact = ps.max_singular_dim(ps.zero_set(S, m))
                    self.assertTrue(exact)
                    self.assertEqual(got, brute_max_singular_dim(S, m), (m, t, c))

    def test_named_examples(self):
        m, tabs = 4, ps.mon_tables(4)
        mons = ps.monomials(4)
        N = len(mons)
        x12 = 1 << mons.index((0, 1))
        x34 = 1 << mons.index((2, 3))
        S = ps.sigma_from_coeffs(x12 | (x34 << N), tabs, 2)   # (x1 x2, x3 x4)
        self.assertEqual(ps.min_codim(S, m), (2, True))
        self.assertEqual(ps.min_codim((0, 0), m), (0, True))
        mons2 = ps.monomials(2)
        aniso = sum(1 << mons2.index(p) for p in [(0, 0), (1, 1), (0, 1)])  # x1 + x2 + x1 x2
        self.assertEqual(ps.min_codim(ps.sigma_from_coeffs(aniso, ps.mon_tables(2), 1), 2),
                         (2, True))


class TestSolver(unittest.TestCase):
    def test_solutions_satisfy_identity_and_others_do_not(self):
        rng = random.Random(4)
        for t, m in ((2, 4), (3, 4)):
            tabs = ps.mon_tables(m)
            N = len(tabs)
            for _ in range(4):
                c = rng.randrange(0, m + 1)
                B = ps.random_subspace([1 << i for i in range(t * t)], c, rng) if c else []
                y = m - c
                mm, at = ps.system(B, y)
                self.assertEqual(mm, m)
                sol = ps.solve_sigma(at, m, t)
                for v in sol:
                    self.assertTrue(ps.identity_holds(at, ps.sigma_from_coeffs(v, tabs, t), m, t))
                while True:
                    v = rng.getrandbits(t * N)
                    if ps.rank_f2(sol + [v]) > ps.rank_f2(sol):
                        break
                self.assertFalse(ps.identity_holds(at, ps.sigma_from_coeffs(v, tabs, t), m, t))

    def test_t1_example_reaches_codimension_1(self):
        # alpha(h) = h_1 on F_2^2 and sigma = h_1 h_2 + h_2 (Lemma 22: codimension 1 is needed).
        mons = ps.monomials(2)
        tabs = ps.mon_tables(2)
        coef = (1 << mons.index((0, 1))) | (1 << mons.index((1, 1)))
        m, at = ps.system([1], 1)
        S = ps.sigma_from_coeffs(coef, tabs, 1)
        self.assertTrue(ps.identity_holds(at, S, m, 1))
        self.assertEqual(ps.min_codim(S, m), (1, True))

    def test_full_action_kills_sigma(self):
        # Lemma 21(c): alpha onto End(X) with t >= 2 forces sigma = 0.
        full2 = [1 << i for i in range(4)]
        for y in range(2):
            m, at = ps.system(full2, y)
            self.assertEqual(ps.solve_sigma(at, m, 2), [])
        m, at = ps.system([1 << i for i in range(9)], 0)
        self.assertEqual(ps.solve_sigma(at, m, 3), [])

    def test_k0_in_radical_on_random_systems(self):
        rng = random.Random(6)
        tabs = {}
        for _ in range(10):
            c = rng.randrange(0, 4)
            B = ps.random_subspace([1 << i for i in range(4)], c, rng) if c else []
            rec = ps.run_system(B, rng.randrange(0, 3), 2, tabs, rng, full_bits=8, samples=16)
            self.assertEqual(rec["k0_violations"], 0)
            self.assertEqual(rec["identity_violations"], 0)


class TestExactParts(unittest.TestCase):
    def test_t1(self):
        st = ps.exact_part(1)
        self.assertEqual(st["max_codim"], 1)
        self.assertTrue(st["exact"])
        self.assertEqual(st["k0_violations"], 0)


if __name__ == "__main__":
    unittest.main()
