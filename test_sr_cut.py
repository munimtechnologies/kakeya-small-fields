# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Exact checks for note a177 (sr_cut.py).  Every assertion is a statement proved in
notes/a177.md (or in a174 and re-checked here); comparisons are exact integer or
Fraction comparisons unless a float margin is stated."""
import itertools
import math
import random
import unittest

import sr_cut as sc


def rand_matrix(rng, q, k, density, zero_diag=False):
    M = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i == j and zero_diag:
                continue
            if i == j or rng.random() < density:
                M[i][j] = rng.randrange(q)
    return M


def band_matrix(rng, q, k, w):
    M = [[0] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if j == i + w:
                M[i][j] = rng.randrange(1, q)
            elif j < i + w:
                M[i][j] = rng.randrange(q)
    return M


class TestBasics(unittest.TestCase):
    def test_zero_matrix_value(self):
        # M = 0: N_y = 2^(#nonzero y_i), H = k (1 - 1/q) exactly.
        for q, k in [(3, 2), (3, 3), (5, 2)]:
            M = [[0] * k for _ in range(k)]
            W = sc.weight(q, M)
            expo = sum(sum(1 for x in y if x) for y in sc.points(q, k))
            self.assertEqual(W, 2 ** expo)

    def test_diagonal_shift_invariance(self):
        # a174 Prop 67(a): H(M + tI) = H(M); here even W(M + tI) = W(M).
        rng = random.Random(1)
        for q, k in [(3, 3), (5, 2), (3, 4)]:
            for _ in range(5):
                M = rand_matrix(rng, q, k, 0.5)
                for t in range(q):
                    self.assertEqual(sc.weight(q, sc.shift_diag(q, M, t)), sc.weight(q, M))


class TestPeeling(unittest.TestCase):
    def test_lemma139_every_order(self):
        rng = random.Random(139)
        cases = [(3, 3, 12), (3, 4, 14), (5, 3, 8)]
        for q, k, reps in cases:
            for r in range(reps):
                M = rand_matrix(rng, q, k, [0.3, 0.5, 0.8][r % 3])
                for order in itertools.permutations(range(k)):
                    f, u, l = sc.peel_counts(q, M, order)
                    self.assertEqual(f + u + l, k)
                    self.assertTrue(sc.peel_bound_holds_exactly(q, M, f, u),
                                    (q, k, M, order, f, u))

    def test_corollary_139_1_determination(self):
        rng = random.Random(1391)
        for q, k in [(3, 3), (3, 4), (5, 3)]:
            for _ in range(10):
                M = rand_matrix(rng, q, k, 0.5)
                for s in range(k + 1):
                    for S in itertools.combinations(range(k), s):
                        if len(sc.closure(q, M, S)) == k:
                            self.assertTrue(sc.determined_by(q, M, S), (q, M, S))


class TestBand(unittest.TestCase):
    def test_theorem63_exhaustive_q3_k3_w1(self):
        q, k = 3, 3
        n = 0
        for m01, m12 in itertools.product(range(1, q), repeat=2):
            for low in itertools.product(range(q), repeat=6):
                M = [[low[0], m01, 0], [low[1], low[2], m12], [low[3], low[4], low[5]]]
                self.assertTrue(sc.is_upper_band(q, M, 1))
                # H(M) <= log2 q, and log2 3 < k (1 - 1/q) = 2: strict SR*.
                self.assertTrue(sc.peel_bound_holds_exactly(q, M, 1, 0), M)
                self.assertTrue(sc.sr_strict_holds_exactly(q, M), M)
                self.assertEqual(len(sc.closure(q, M, [0])), k)
                n += 1
        self.assertEqual(n, 4 * 729)

    def test_theorem63_random(self):
        rng = random.Random(63)
        for q, k, w in [(3, 4, 1), (3, 4, 2), (5, 3, 1), (5, 3, 2), (7, 2, 1)]:
            for _ in range(12):
                M = band_matrix(rng, q, k, w)
                self.assertTrue(sc.is_upper_band(q, M, w))
                self.assertTrue(sc.peel_bound_holds_exactly(q, M, w, 0), (q, M, w))
                self.assertEqual(len(sc.closure(q, M, range(w))), k)

    def test_prop71_cyclic_tridiagonal(self):
        # rows read i-1, i, i+1 (mod k), M[i][i+1] != 0: H(M) <= 2 log2 q.
        rng = random.Random(71)
        for q, k in [(3, 3), (3, 4), (5, 3)]:
            for _ in range(10):
                M = [[0] * k for _ in range(k)]
                for i in range(k):
                    M[i][i] = rng.randrange(q)
                    M[i][(i - 1) % k] = rng.randrange(q)
                    M[i][(i + 1) % k] = rng.randrange(1, q)
                self.assertTrue(sc.peel_bound_holds_exactly(q, M, 2, 0), M)
                self.assertEqual(len(sc.closure(q, M, [0, 1])), k)


class TestCut(unittest.TestCase):
    def test_lemma140_all_cuts(self):
        rng = random.Random(140)
        for q, k, reps in [(3, 3, 10), (3, 4, 10), (5, 3, 6)]:
            for r in range(reps):
                M = rand_matrix(rng, q, k, [0.25, 0.5, 0.75][r % 3])
                for s in range(1, k):
                    for S in itertools.combinations(range(k), s):
                        self.assertTrue(sc.cut_bound_holds_exactly(q, M, S), (q, M, S))

    def test_lemma140_rank_zero_is_prop67b(self):
        # block lower-triangular: rows of S read nothing outside S.
        rng = random.Random(670)
        q, k = 3, 4
        for _ in range(8):
            M = rand_matrix(rng, q, k, 0.6)
            M[0][2] = M[0][3] = M[1][2] = M[1][3] = 0
            self.assertEqual(sc.cut_rank(q, M, [0, 1]), 0)
            self.assertTrue(sc.cut_bound_holds_exactly(q, M, [0, 1]))


class TestExpansion(unittest.TestCase):
    def test_pair_count_identity_and_rank_bound(self):
        rng = random.Random(58)
        for q, k in [(3, 2), (3, 3), (3, 4), (5, 2), (5, 3)]:
            for r in range(6):
                M = rand_matrix(rng, q, k, [0.3, 0.6, 1.0][r % 3])
                EN = sc.mean_fibre(q, M)
                self.assertEqual(EN, sc.pair_count_mean(q, M))
                self.assertLessEqual(EN, sc.expansion_sum(q, M))
                # Jensen: H(M) <= log2 E N (float, margin 1e-9).
                self.assertLessEqual(sc.entropy(q, M), math.log2(float(EN)) + 1e-9)

    def test_theorem64_ratios(self):
        r1, r2 = sc.ratios(3)
        self.assertLess(r1, 0.9270)
        self.assertLess(r2, 0.8655)
        for k in range(7, 400):
            self.assertLess(r1 ** k + r2 ** k, 0.96)
        for q in range(5, 300, 2):
            a, b = sc.ratios(q)
            self.assertLess(max(a, b), 0.8616)
            for k in range(5, 60):
                self.assertLess(a ** k + b ** k, 0.96)

    def test_theorem64_exhaustive_q3_k3(self):
        # every zero-diagonal M over F_3 with k = 3 that is half-expanding satisfies strict SR*.
        q, k = 3, 3
        off = [(i, j) for i in range(k) for j in range(k) if i != j]
        count = 0
        for vals in itertools.product(range(q), repeat=len(off)):
            M = [[0] * k for _ in range(k)]
            for (i, j), v in zip(off, vals):
                M[i][j] = v
            if sc.half_expanding(q, M):
                count += 1
                self.assertTrue(sc.sr_strict_holds_exactly(q, M), M)
        self.assertGreater(count, 0)

    def test_theorem64_random_q3_k4_q5_k3(self):
        rng = random.Random(64)
        for q, k in [(3, 4), (5, 3)]:
            seen = 0
            for _ in range(40):
                M = rand_matrix(rng, q, k, 0.8, zero_diag=True)
                if sc.half_expanding(q, M):
                    seen += 1
                    self.assertTrue(sc.sr_strict_holds_exactly(q, M), (q, M))
            self.assertGreater(seen, 0)

    def test_corollary64_1_bound_tends_to_zero(self):
        self.assertLess(sc.generic_failure_bound(3, 60), 0.2)
        self.assertLess(sc.generic_failure_bound(3, 120), 1e-3)
        self.assertLess(sc.generic_failure_bound(5, 60), 0.01)


class TestErratum(unittest.TestCase):
    def test_a176_prop70_constant(self):
        v = 2 * math.log2(5 / 4)
        self.assertLess(v, 0.644)
        self.assertGreater(v, 0.6438)
        self.assertGreater(v, 0.64)


if __name__ == '__main__':
    unittest.main()
