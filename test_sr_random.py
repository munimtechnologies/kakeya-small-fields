# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Exact checks for note a178 (sr_random.py).  Every assertion is a statement proved in
notes/a178.md; comparisons are exact integer or Fraction comparisons unless a float
margin is stated."""
import itertools
import math
import random
import unittest
from fractions import Fraction

import sr_random as sr


def homogeneous(k, p):
    return [[Fraction(p)] * k for _ in range(k)]


def all_matrices(q, k):
    off = sr.off_diagonal(k)
    for vals in itertools.product(range(q), repeat=len(off)):
        M = [[0] * k for _ in range(k)]
        for (i, j), v in zip(off, vals):
            M[i][j] = v
        yield M


class TestLemma141(unittest.TestCase):
    def test_homogeneous_identity(self):
        cases = [(3, 2), (3, 3), (5, 2), (7, 2)]
        for q, k in cases:
            for p in [Fraction(0), Fraction(1, 5), Fraction(1, 2), Fraction(q - 1, q),
                      Fraction(9, 10), Fraction(1)]:
                brute = sr.annealed_bruteforce(q, k, homogeneous(k, p))
                self.assertEqual(brute, sr.annealed_formula(q, k, homogeneous(k, p)))
                self.assertEqual(brute, sr.S(q, k, p), (q, k, p))

    def test_inhomogeneous_identity(self):
        rng = random.Random(141)
        for q, k in [(3, 3), (5, 2), (3, 2)]:
            for _ in range(3):
                P = [[Fraction(rng.randrange(0, 11), 10) for _ in range(k)] for _ in range(k)]
                self.assertEqual(sr.annealed_bruteforce(q, k, P), sr.annealed_formula(q, k, P))

    def test_diagonal_does_not_matter(self):
        p = Fraction(1, 3)
        for q, k, diag in [(3, 3, [1, 2, 0]), (5, 2, [3, 4])]:
            self.assertEqual(sr.annealed_bruteforce(q, k, homogeneous(k, p), diag=diag),
                             sr.S(q, k, p))

    def test_jensen_every_matrix_q3_k3(self):
        for M in all_matrices(3, 3):
            self.assertTrue(sr.jensen_holds_exactly(3, M), M)


class TestTheorem65Dense(unittest.TestCase):
    def test_closed_form(self):
        for q in [3, 5, 7, 11]:
            for k in range(1, 40):
                self.assertEqual(sr.S(q, k, Fraction(q - 1, q)), 2 - Fraction(1, q ** k))

    def test_uniform_average_and_tail_q3_k3(self):
        q, k = 3, 3
        mats = list(all_matrices(q, k))
        avg = sum(sr.mean_fibre(q, M) for M in mats) / len(mats)
        self.assertEqual(avg, 2 - Fraction(1, 27))
        # P(H(M) >= s) <= (2 - q^-k) 2^-s for s = 1, 2.
        for s in [1, 2]:
            frac = Fraction(sum(1 for M in mats if sr.entropy_at_least(q, M, s)), len(mats))
            self.assertLessEqual(frac, (2 - Fraction(1, 27)) / 2 ** s)

    def test_uniform_average_q5_q7_k2(self):
        for q in [5, 7]:
            mats = list(all_matrices(q, 2))
            avg = sum(sr.mean_fibre(q, M) for M in mats) / len(mats)
            self.assertEqual(avg, 2 - Fraction(1, q * q))


class TestTheorem66Sparse(unittest.TestCase):
    def test_ratio_constants(self):
        for q in range(3, 300, 2):
            rA, rB = sr.ratios(q)
            self.assertLess(rA, 0.9582)
            self.assertLess(rB, 0.9739)
            self.assertLessEqual(0.2, ((q - 1) / q) / (1 + (q - 1) / q))  # Chernoff range
            # negative-lambda case: (1 + 1/q) / b <= 0.8400 and 1/b <= 0.63.
            b = 2 ** (1 - 1 / q)
            self.assertLess((1 + 1 / q) / b, 0.8400)
            self.assertLess(1 / b, 0.63)
        # q >= 300 analytically: a <= 1 and b >= 2^(299/300).
        self.assertLess(2 ** 0.7219281 / 2 ** (299 / 300), 0.9582)
        self.assertLess((1 + math.exp(-0.2)) / 2 ** (299 / 300), 0.9739)
        self.assertLess(sr.H2(0.2), 0.72193)

    def test_split_bound_exact_and_float_tail(self):
        for q in [3, 5, 7]:
            a = (q - 1) / q
            for k in range(1, 61):
                for p in [Fraction(1, k), Fraction(2, k), Fraction(5, k), Fraction(1, 3)]:
                    if p > Fraction(q - 1, q) or p * k < 1:
                        continue
                    s = sr.S(q, k, p)
                    head, tail, t0, lam = sr.split_bound(q, k, p)
                    self.assertLessEqual(s, head + tail)
                    # Chernoff head bound and lambda^t0 <= e^(-1/5) (floats, margin).
                    self.assertLessEqual(float(head),
                                         (2 ** (sr.H2(0.2) + 0.2 * math.log2(a))) ** k * (1 + 1e-9))
                    self.assertLessEqual(float(lam) ** t0, math.exp(-0.2) + 1e-12)
                    self.assertLessEqual(float(tail), (1 + a * math.exp(-0.2)) ** k * (1 + 1e-9))

    def test_negative_lambda_case(self):
        for q in [3, 5, 7]:
            for k in range(1, 30):
                for p in [Fraction(q - 1, q) + Fraction(1, 100), Fraction(9, 10), Fraction(1)]:
                    if p > 1 or p <= Fraction(q - 1, q):
                        continue
                    self.assertLessEqual(sr.S(q, k, p), 1 + Fraction(q + 1, q) ** k)

    def test_failure_probability_below_one_at_average_degree_one(self):
        # S < b^k  <=>  S^q < 2^(k (q-1)), exact.
        for q, k in [(3, 30), (3, 40), (3, 60), (5, 30)]:
            s = sr.S(q, k, Fraction(1, k))
            self.assertLess(s ** q, 2 ** (k * (q - 1)), (q, k))

    def test_monotone_in_p_for_nonnegative_lambda(self):
        for q in [3, 5]:
            for k in [5, 12, 20]:
                ps = [Fraction(i, 20) for i in range(0, 21) if Fraction(i, 20) <= Fraction(q - 1, q)]
                vals = [sr.S(q, k, p) for p in ps]
                for x, y in zip(vals, vals[1:]):
                    self.assertGreaterEqual(x, y)
                self.assertEqual(vals[0], Fraction(2 * q - 1, q) ** k)  # p = 0: DKSS level


class TestProposition72Patterns(unittest.TestCase):
    def pattern_check(self, q, k, arcs):
        values = {(i, j): (range(1, q) if (i, j) in arcs else [0]) for (i, j) in sr.off_diagonal(k)}
        P = [[Fraction(1) if (i, j) in arcs else Fraction(0) for j in range(k)] for i in range(k)]
        brute = sr.annealed_bruteforce(q, k, P, values=values)
        self.assertEqual(brute, sr.annealed_formula(q, k, P))
        self.assertEqual(brute, sr.pattern_sum(q, k, arcs))
        self.assertLessEqual(brute, sr.fort_bound(q, k, arcs))

    def test_patterns(self):
        cyc4 = {(0, 1), (1, 2), (2, 3), (3, 0)}
        two_out = {(0, 1), (0, 2), (1, 2), (1, 3), (2, 3), (2, 0), (3, 0), (3, 1)}
        complete3 = set(sr.off_diagonal(3))
        self.pattern_check(3, 4, cyc4)
        self.pattern_check(3, 4, two_out)
        self.pattern_check(3, 3, complete3)
        self.pattern_check(5, 3, {(0, 1), (1, 2), (2, 0), (0, 2)})

    def test_single_arc_kills_term(self):
        for q in [3, 5, 7]:
            self.assertEqual(sr.pi_pattern(q, 0), 1)
            self.assertEqual(sr.pi_pattern(q, 1), 0)
            for m in range(2, 12):
                self.assertGreaterEqual(sr.pi_pattern(q, m), 0)
                self.assertLessEqual(sr.pi_pattern(q, m), Fraction(1, q - 1))


class TestProposition73FortsOnly(unittest.TestCase):
    def test_nonforts_have_no_pairs_and_rank_bound(self):
        rng = random.Random(73)
        for q, k, reps in [(3, 3, 10), (3, 4, 10), (5, 3, 6)]:
            for r in range(reps):
                dens = [0.3, 0.5, 0.8][r % 3]
                M = [[(rng.randrange(1, q) if rng.random() < dens else 0) if i != j
                      else rng.randrange(q) for j in range(k)] for i in range(k)]
                arcs = sr.arcs_of(M)
                total = Fraction(0)
                for t in range(k + 1):
                    for T in itertools.combinations(range(k), t):
                        v = sr.V(q, M, T)
                        if t > 0 and not sr.is_fort(k, arcs, T):
                            self.assertEqual(v, 0, (M, T))
                        self.assertLessEqual(v, (q - 1) ** (t - sr.rho(q, M, T)))
                        total += Fraction(v, q ** t)
                self.assertEqual(total, sr.mean_fibre(q, M))

    def test_exhaustive_q3_k3(self):
        q, k = 3, 3
        count = 0
        for M in all_matrices(q, k):
            if sr.fort_half_expanding(q, M):
                count += 1
                self.assertTrue(sr.sr_strict_holds_exactly(q, M), M)
        self.assertGreater(count, 0)

    def test_hypothesis_forces_strong_connectivity(self):
        # a set T read by no outside row is a fort with rho(T) = 0.
        for M in all_matrices(3, 3):
            arcs = sr.arcs_of(M)
            for t in (1, 2):
                for T in itertools.combinations(range(3), t):
                    if not any((i, j) in arcs for i in range(3) if i not in T for j in T):
                        self.assertTrue(sr.is_fort(3, arcs, T))
                        self.assertEqual(sr.rho(3, M, T), 0)
                        self.assertFalse(sr.fort_half_expanding(3, M))


if __name__ == '__main__':
    unittest.main()
