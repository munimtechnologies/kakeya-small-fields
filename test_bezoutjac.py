"""Tests for note a170 (Bezout-Jacobian bound). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion checks a fact proved in a170.md. All q are odd primes.
"""
import math
import random
import unittest

import bezoutjac as bj

SIZES = [(3, 1), (5, 1), (7, 1), (3, 2), (5, 2), (7, 2), (3, 3), (5, 3)]
EPS = 1e-9


def check_bound(tc, table, q, k):
    lam, gsum, sums, b2 = bj.bezout_data(table, q, k)
    n = q ** k
    # Lemma 125: every fibre of every A_t has sum_{y in F} 2^{c_t(y)} <= 2^k.
    tc.assertLessEqual(max(sums), 2 ** k)
    # Theorem 50 (strong form) and (Jensen form).
    tc.assertLessEqual(lam, b2 + EPS)
    tc.assertLessEqual(b2, q * k - gsum / n + EPS)
    # g(J) <= k at every point.
    tc.assertLessEqual(gsum, k * n)
    return lam, gsum, sums


class TestRank(unittest.TestCase):
    def test_rank_small(self):
        self.assertEqual(bj.rank_mod([[1, 2], [2, 4]], 5), 1)
        self.assertEqual(bj.rank_mod([[1, 2], [3, 4]], 5), 2)
        self.assertEqual(bj.rank_mod([[0, 0], [0, 0]], 3), 0)
        self.assertEqual(bj.rank_mod([[1, 1, 1], [1, 2, 0], [2, 0, 1]], 3), 2)

    def test_modulus_irreducible(self):
        for q in (3, 5, 7):
            for k in (2, 3):
                m = bj.irreducible_modulus(q, k)
                self.assertEqual(m[-1], 1)
                for s in range(q):
                    self.assertNotEqual(sum(m[j] * pow(s, j, q) for j in range(k + 1)) % q, 0)


class TestFrame(unittest.TestCase):
    """Proposition 57: frame products are tight in every fibre and globally."""

    def test_frame_equality(self):
        rng = random.Random(1701)
        for q, k in SIZES:
            for _ in range(3):
                table = bj.table_of(bj.frame_map(q, k, rng), q, k)
                lam, gsum, sums = check_bound(self, table, q, k)
                n = q ** k
                self.assertEqual(gsum, k * n)
                self.assertTrue(all(s == 2 ** k for s in sums))
                self.assertAlmostEqual(lam, k * (q - 1), delta=1e-9)
                self.assertAlmostEqual(lam, q * k - gsum / n, delta=1e-9)


class TestMixed(unittest.TestCase):
    """Theorem 50 on S sq(Tx) + Lx + c and S (Tx)^2 + Lx + c in F_q[s]/(m)."""

    def test_mixed_frame(self):
        rng = random.Random(1702)
        for q, k in SIZES:
            for _ in range(4):
                table = bj.table_of(bj.mixed_frame_map(q, k, rng), q, k)
                check_bound(self, table, q, k)

    def test_mixed_field(self):
        rng = random.Random(1703)
        for q, k in SIZES:
            if k < 2:
                continue
            for _ in range(4):
                table = bj.table_of(bj.mixed_field_map(q, k, rng), q, k)
                check_bound(self, table, q, k)

    def test_random_plane(self):
        rng = random.Random(1704)
        for q in (3, 5, 7):
            for _ in range(8):
                table = bj.table_of(bj.random_plane_quadratic(q, rng), q, 2)
                check_bound(self, table, q, 2)


class TestExamples(unittest.TestCase):
    def test_swap(self):
        """Proposition 58: for (x2^2, x1^2), sum_x g = q^2 + 1."""
        for q in (3, 5, 7, 11):
            table = bj.table_of(bj.swap_map, q, 2)
            lam, gsum, sums = check_bound(self, table, q, 2)
            self.assertEqual(gsum, q * q + 1)
            self.assertLessEqual(lam, 2 * (q - 1) + EPS)  # Theorem 38, for comparison

    def test_field_square(self):
        """Proposition 59: squaring in F_(q^k): sum_x g = kq, Lambda = q - q^(1-k)."""
        for q, k in [(3, 2), (5, 2), (7, 2), (11, 2), (3, 3), (5, 3)]:
            table = bj.table_of(bj.field_square_map(q, k), q, k)
            lam, gsum, sums = check_bound(self, table, q, k)
            self.assertEqual(gsum, k * q)
            self.assertAlmostEqual(lam, q - q ** (1 - k), delta=1e-9)
            gap = (q * k - gsum / q ** k) - lam
            self.assertAlmostEqual(gap, q * k - k * q ** (1 - k) - q + q ** (1 - k), delta=1e-9)

    def test_one_dim(self):
        """Corollary 50.2: every quadratic map of F_q has g = 1 at every point."""
        rng = random.Random(1705)
        for q in (3, 5, 7, 11, 13):
            for _ in range(3):
                table = bj.table_of(bj.frame_map(q, 1, rng), q, 1)
                lam, gsum, sums = check_bound(self, table, q, 1)
                self.assertEqual(gsum, q)
                self.assertAlmostEqual(lam, q - 1, delta=1e-9)


if __name__ == "__main__":
    unittest.main()
