# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m3_exact as mx


def example1():
    # Example 1 of finite-groups.md: t = 3, V = F_2^2, A_1 = E_11, A_2 = E_12 + E_13 + E_21 + E_22.
    A1 = mx.entries(3, [(0, 0)])
    A2 = mx.entries(3, [(0, 1), (0, 2), (1, 0), (1, 1)])
    return [0, A1, A2, A1 ^ A2], [0, 6, 7, 3]


def diagonal_system(t):
    # Lemma 23(d): V = F_2^(2t) with coordinates (u, v), A_h = diag(u), sigma_i = (1 + u_i) v_i.
    m = 2 * t
    at, sv = [], []
    for h in range(1 << m):
        u, v = h & ((1 << t) - 1), h >> t
        at.append(sum(1 << (t * i + i) for i in range(t) if (u >> i) & 1))
        sv.append(sum(1 << i for i in range(t) if not (u >> i) & 1 and (v >> i) & 1))
    return m, at, sv


class TestMatrices(unittest.TestCase):
    def test_rank_fix(self):
        E11 = mx.entries(3, [(0, 0)])
        self.assertEqual((mx.mat_rank(E11, 3), mx.fix_dim(E11, 3)), (1, 1))
        self.assertEqual(len(mx.kernel_basis(E11, 3)), 2)
        self.assertEqual((mx.mat_rank(mx.identity(3), 3), mx.fix_dim(mx.identity(3), 3)), (3, 3))
        self.assertEqual((mx.mat_rank(0, 3), mx.fix_dim(0, 3)), (0, 0))
        N = mx.entries(3, [(0, 1), (1, 2)])          # nilpotent of rank 2, so Fix(N) = 0
        self.assertEqual((mx.mat_rank(N, 3), mx.fix_dim(N, 3)), (2, 0))
        A2 = mx.entries(3, [(0, 1), (0, 2), (1, 0), (1, 1)])
        self.assertEqual(mx.kernel_basis(A2, 3), [7])


class TestLemma26(unittest.TestCase):
    def test_example1(self):
        at, sv = example1()
        self.assertTrue(mx.is_system(at, sv, 2, 3))
        self.assertEqual(mx.zero_set(sv), 0)                 # anisotropic
        self.assertFalse(mx.is_system(at, [0, 6, 7, 2], 2, 3))   # control
        for u, rank in ((1, 1), (2, 2), (3, 2)):
            r = mx.lemma26_at(at, sv, 2, 3, u)
            self.assertTrue(r["inside"])
            self.assertTrue(r["system"])
            self.assertEqual((r["rank"], r["codim"]), (rank, 1))

    def test_diagonal(self):
        for t in (2, 3):
            m, at, sv = diagonal_system(t)
            self.assertTrue(mx.is_system(at, sv, m, t))
            xm = mx.xor_masks(m)
            self.assertEqual(mx.least_codim(mx.zero_set(sv), m, xm), (t, True))
            for u in range(1, 1 << m):
                r = mx.lemma26_at(at, sv, m, t, u)
                self.assertTrue(r["inside"])
                self.assertTrue(r["system"])
                if sv[u] == 0:
                    self.assertLessEqual(r["codim"], r["fix"])
                    self.assertLessEqual(r["fix"], r["rank"])

    def test_random_systems(self):
        # Lemma 26 at every u, and Theorem 24 (M(2) = 2, M(3) = 3) on random solutions.
        rng = random.Random(7)
        xms = {m: mx.xor_masks(m) for m in range(0, 6)}
        for t, count in ((2, 10), (3, 14)):
            for _ in range(count):
                c = rng.randint(1, 3)
                B = mx.random_subspace(rng, t * t, c)
                y = rng.randint(0, min(t, 5 - c))
                m, at = mx.system(B, y)
                tabs = mx.mon_tables(m)
                sol = mx.solve_sigma(at, m, t)
                for _ in range(2 if sol else 0):
                    v = mx.combine(sol, rng.getrandbits(len(sol)))
                    sv = mx.table(mx.sigma_from_coeffs(v, tabs, t), m)
                    self.assertTrue(mx.is_system(at, sv, m, t))
                    lc, ex = mx.least_codim(mx.zero_set(sv), m, xms[m])
                    self.assertTrue(ex)
                    self.assertLessEqual(lc, t)
                    for u in range(1, 1 << m):
                        r = mx.lemma26_at(at, sv, m, t, u)
                        self.assertTrue(r["inside"])
                        self.assertTrue(r["system"])
                        if sv[u] == 0:
                            self.assertLessEqual(r["codim"], r["fix"])
                            self.assertLessEqual(r["fix"], r["rank"])

    def test_invertible_element(self):
        # Lemma 26(c): with A_u invertible, sigma vanishes on U, of codimension <= t.
        rng = random.Random(5)
        w = mx.entries(3, [(1, 0), (2, 1), (0, 2), (1, 2)])      # order 7
        for B, y in (([w], 2), ([w, mx.entries(3, [(0, 0)])], 1), ([mx.identity(3)], 2)):
            m, at = mx.system(B, y)
            tabs = mx.mon_tables(m)
            sol = mx.solve_sigma(at, m, 3)
            for i in range(min(1 << len(sol), 32)):
                sv = mx.table(mx.sigma_from_coeffs(mx.combine(sol, i), tabs, 3), m)
                r = mx.lemma26_at(at, sv, m, 3, 1)
                self.assertEqual(r["d"], 0)
                self.assertTrue(r["inside"])                    # X1 = 0, so sigma(U) = 0
                self.assertLessEqual(r["codim"], 3)


class TestRankOne(unittest.TestCase):
    def test_common_image_and_kernel(self):
        xms = {m: mx.xor_masks(m) for m in range(0, 6)}
        for t in (2, 3):
            image = [mx.entries(t, [(0, c)]) for c in range(t)]
            kernel = [mx.entries(t, [(r, 0)]) for r in range(t)]
            for y in (0, 1):
                for kind, gens in (("image", image), ("kernel", kernel)):
                    m, at = mx.system(gens, y)
                    tabs = mx.mon_tables(m)
                    sol = mx.solve_sigma(at, m, t)
                    for i in range(min(1 << len(sol), 64)):
                        sv = mx.table(mx.sigma_from_coeffs(mx.combine(sol, i), tabs, t), m)
                        if kind == "image":
                            for h in range(1 << m):
                                for hp in range(1 << m):
                                    self.assertEqual((sv[h ^ hp] ^ sv[h] ^ sv[hp]) >> 1, 0)
                        else:
                            zq = sum(1 << h for h in range(1, 1 << m) if not sv[h] & 1)
                            self.assertEqual(mx.has_vanishing(zq, m - 2, xms[m]), (True, True))


class TestCases(unittest.TestCase):
    def test_bounds(self):
        self.assertEqual(mx.a_bounds(6), [0, 1, 2, 3, 6, 8, 12])
        self.assertEqual(mx.e_bounds(6), [0, 0, 0, 0, 2, 3, 6])

    def test_corollary14(self):
        for a in range(1, 15):
            for b in range(0, 13):
                self.assertEqual(mx.settled(a, b), b <= 1 or a <= max(7, b + 2), (a, b))
        self.assertTrue(mx.settled(7, 2) and mx.settled(6, 3) and mx.settled(10, 8))
        self.assertFalse(mx.settled(8, 2) or mx.settled(8, 5) or mx.settled(9, 6))
        out = mx.cases()
        self.assertTrue(all(out["graded"].values()))
        self.assertEqual(out["first_open"]["2"], 8)


if __name__ == "__main__":
    unittest.main()
