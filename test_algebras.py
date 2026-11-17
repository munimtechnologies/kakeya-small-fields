"""Tests for note a172 (quadratic Kakeya blocks as commutative algebras). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion checks a fact proved in a172.md. All q are odd primes. Lambda is computed by
brute force over every point and every t, so the tests do not rely on the proofs.
"""
import math
import random
import unittest

import algebras as al

EPS = 1e-9


def ell_matrix(C, q, rng):
    """L = R_l for a random l in A."""
    k = len(C)
    l = tuple(rng.randrange(q) for _ in range(k))
    return al.mult_matrix(C, l, q)


def rand_const(q, k, rng):
    return tuple(rng.randrange(q) for _ in range(k))


class TestUnitReduction(unittest.TestCase):
    """Lemma 127: if the polar algebra has a unit e, A_t(x) = P(x + t e / 2) + const, so every
    A_t has the same fibre sizes as P and Lambda(P) = q H(X | P(X)). Any L, any c."""

    def check(self, C, q, L, c):
        k = len(C)
        self.assertIsNotNone(al.find_unit(C, q))
        P = al.make_map(C, q, L, c)
        base = al.fibre_sizes(P, q, k)
        for t in range(q):
            self.assertEqual(al.fibre_sizes(al.shifted(P, q, t), q, k), base)
        lam = al.kakeya_lambda(P, q, k)
        self.assertAlmostEqual(lam, q * al.cond_entropy(P, q, k), delta=EPS)

    def test_random_unital_algebras(self):
        rng = random.Random(1721)
        for q, k, reps in [(3, 2, 12), (3, 3, 10), (3, 4, 4), (5, 2, 10), (5, 3, 4), (7, 2, 6)]:
            for _ in range(reps):
                C = al.random_unital(q, k, rng)
                self.check(C, q, al.random_matrix(q, k, rng), rand_const(q, k, rng))

    def test_frames_with_general_linear_part(self):
        rng = random.Random(1722)
        for q, k in [(3, 2), (3, 3), (5, 2), (5, 3), (7, 2)]:
            for _ in range(4):
                a = [rng.randrange(1, q) for _ in range(k)]
                C = al.frame_algebra(q, a)
                self.check(C, q, al.random_matrix(q, k, rng), rand_const(q, k, rng))

    def test_fields(self):
        rng = random.Random(1723)
        for q, f in [(3, [1, 0, 1]), (5, [2, 0, 1]), (7, [1, 0, 1]), (3, [1, 2, 0, 1])]:
            self.assertTrue(al.is_irreducible(f, q))
            C = al.poly_algebra(f, q)
            k = len(C)
            self.check(C, q, al.random_matrix(q, k, rng), rand_const(q, k, rng))


class TestAssociative(unittest.TestCase):
    """Theorem 53: for every commutative associative algebra A (unital or not) of dimension k,
    q odd, l in A and c, P(x) = x^2 + l x + c has Lambda <= k(q-1), with equality iff A is
    isomorphic to F_q^k."""

    def test_all_monogenic(self):
        # F_q[s]/(f) for EVERY monic f of degree k; A = F_q^k iff f has k distinct roots in F_q.
        rng = random.Random(1731)
        for q, kmax in [(3, 4), (5, 3), (7, 2)]:
            for k in range(1, kmax + 1):
                for f in al.monic_polys(q, k):
                    C = al.poly_algebra(f, q)
                    if k <= 3:
                        self.assertTrue(al.is_associative(C, q))
                    L = ell_matrix(C, q, rng)
                    P = al.make_map(C, q, L, rand_const(q, k, rng))
                    lam = al.kakeya_lambda(P, q, k)
                    self.assertLessEqual(lam, k * (q - 1) + EPS)
                    split = len(al.poly_roots(f, q)) == k
                    self.assertEqual(abs(lam - k * (q - 1)) < EPS, split, (q, f, lam))
                    if not split:
                        self.assertLess(lam, k * (q - 1) - 1e-3)

    def test_square_zero_local(self):
        rng = random.Random(1732)
        for q, m in [(3, 1), (3, 2), (3, 3), (5, 1), (5, 2), (7, 1)]:
            C = al.square_zero_local(q, m)
            k = m + 1
            self.assertTrue(al.is_associative(C, q))
            P = al.make_map(C, q, ell_matrix(C, q, rng), rand_const(q, k, rng))
            lam = al.kakeya_lambda(P, q, k)
            self.assertAlmostEqual(lam, al.lambda_square_zero(q, m), delta=EPS)
            self.assertLess(lam, k * (q - 1) - 1e-3)

    def test_nilpotent_part(self):
        # Lemma 128: for nilpotent N and l in N, A_t is injective for t != 0, and
        # Lambda = H(Y | Y^2 + l Y) <= dim N log2 q < dim N (q - 1).
        rng = random.Random(1733)
        for q, k in [(3, 1), (3, 2), (3, 3), (3, 4), (5, 1), (5, 2), (5, 3), (7, 2)]:
            C = al.nil_truncated(q, k)
            self.assertTrue(al.is_associative(C, q))
            self.assertIsNone(al.find_unit(C, q))
            for _ in range(3):
                L = ell_matrix(C, q, rng)
                P = al.make_map(C, q, L, rand_const(q, k, rng))
                terms = al.lambda_terms(P, q, k)
                for t in range(1, q):
                    self.assertAlmostEqual(terms[t], 0.0, delta=EPS)
                self.assertLessEqual(terms[0], k * math.log2(q) + EPS)
                self.assertLess(sum(terms), k * (q - 1) - 1e-3)

    def test_products_with_nilpotent(self):
        rng = random.Random(1734)
        cases = [(3, [0, 1, 1], 1), (3, [2, 0, 1], 2), (5, [1, 0, 1], 1), (3, [0, 0, 1], 1)]
        for q, f, n in cases:
            C = al.product(al.poly_algebra(f, q), al.nil_truncated(q, n))
            k = len(C)
            self.assertTrue(al.is_associative(C, q))
            self.assertIsNone(al.find_unit(C, q))
            for _ in range(2):
                P = al.make_map(C, q, ell_matrix(C, q, rng), rand_const(q, k, rng))
                lam = al.kakeya_lambda(P, q, k)
                self.assertLess(lam, k * (q - 1) - 1e-3)

    def test_split_products(self):
        rng = random.Random(1735)
        for q, k in [(3, 2), (3, 3), (5, 2), (5, 3), (7, 2)]:
            C = al.frame_algebra(q, [1] * k)
            P = al.make_map(C, q, ell_matrix(C, q, rng), rand_const(q, k, rng))
            self.assertAlmostEqual(al.kakeya_lambda(P, q, k), k * (q - 1), delta=EPS)


class TestExactValues(unittest.TestCase):
    """Corollary 53.1 and Proposition 63: closed forms."""

    def test_fields(self):
        for q, f in [(3, [1, 0, 1]), (3, [1, 2, 0, 1]), (3, [2, 0, 0, 1, 1]), (5, [2, 0, 1]),
                     (5, [1, 1, 0, 1]), (7, [1, 0, 1])]:
            k = len(f) - 1
            self.assertTrue(al.is_irreducible(f, q))
            C = al.poly_algebra(f, q)
            lam = al.kakeya_lambda(al.make_map(C, q), q, k)
            self.assertAlmostEqual(lam, al.lambda_field(q, k), delta=EPS)

    def test_truncated(self):
        rng = random.Random(1741)
        for q, k in [(3, 1), (3, 2), (3, 3), (3, 4), (3, 5), (5, 1), (5, 2), (5, 3), (7, 2),
                     (7, 3)]:
            C = al.truncated(q, k)
            P = al.make_map(C, q, ell_matrix(C, q, rng), rand_const(q, k, rng))
            lam = al.kakeya_lambda(P, q, k)
            self.assertAlmostEqual(lam, al.lambda_truncated(q, k), delta=EPS)
        # dual numbers: q - 1 + log2 q
        for q in [3, 5, 7, 11]:
            self.assertAlmostEqual(al.lambda_truncated(q, 2), q - 1 + math.log2(q), delta=EPS)


class TestUnitization(unittest.TestCase):
    """Proposition 62: Lambda(P) <= Lambda(P+) <= Lambda(P) + q - 1, with
    Lambda(P+) = Lambda(P) + q - 1 when L = 0."""

    def pair(self, C, q, L):
        k = len(C)
        P = al.make_map(C, q, L)
        D = al.unitization(C)
        self.assertIsNotNone(al.find_unit(D, q))
        Pp = al.make_map(D, q, al.extend_linear(L))
        return al.kakeya_lambda(P, q, k), al.kakeya_lambda(Pp, q, k + 1)

    def test_random_algebras(self):
        rng = random.Random(1751)
        for q, k, reps in [(3, 1, 4), (3, 2, 8), (3, 3, 4), (5, 1, 4), (5, 2, 4)]:
            for _ in range(reps):
                C = al.random_commutative(q, k, rng)
                zero = [[0] * k for _ in range(k)]
                lam, lamp = self.pair(C, q, zero)
                self.assertAlmostEqual(lamp, lam + q - 1, delta=EPS)
                lam, lamp = self.pair(C, q, al.random_matrix(q, k, rng))
                self.assertLessEqual(lam, lamp + EPS)
                self.assertLessEqual(lamp, lam + q - 1 + EPS)

    def test_g_maps(self):
        # a167's degenerate maps G_n: Lambda(G_n+) = Lambda(G_n) + q - 1.
        for q, phi in [(3, [[1, 0], [0, 1]]), (3, [[1, 0], [0, 2]]), (5, [[1, 0], [0, 2]]),
                       (3, [[1, 0, 0], [0, 1, 0], [0, 0, 1]])]:
            C = al.g_map_algebra(q, phi)
            k = len(C)
            zero = [[0] * k for _ in range(k)]
            lam, lamp = self.pair(C, q, zero)
            self.assertAlmostEqual(lamp, lam + q - 1, delta=EPS)


if __name__ == "__main__":
    unittest.main()
