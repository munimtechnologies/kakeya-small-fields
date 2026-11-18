"""Exact checks for note a179 (the fort polynomial).

MV2 of Munim, Inc. Made with AI agents working in MV2's name.
SPDX-License-Identifier: Apache-2.0
Run: python -m unittest test_fortpoly -v
"""
import random
import unittest
from fractions import Fraction
from math import exp, log, log2

from fortpoly import (H2, V, conj_map, digraph_of, expected_fort_poly, fibre_counts,
                      fort_poly, frame_stats, h_one, is_fort, limit_exponent, packing_factor,
                      packing_poly, pi_m, popcount, r_head, r_mid, r_tail, slice_matrix,
                      sum_and_product)


def rand_sparse(rng, q, k, zero_prob):
    rows = []
    for i in range(k):
        row = []
        for j in range(k):
            if rng.random() < zero_prob:
                row.append(0)
            else:
                row.append(rng.randrange(1, q))
        rows.append(row)
    return rows


def all_digraph_average(q, k, p):
    """Exact E_G fort_poly(G) for G ~ D(k, p), by enumerating every digraph."""
    arcs = [(i, j) for i in range(k) for j in range(k) if i != j]
    n = len(arcs)
    pp = [p ** e for e in range(n + 1)]
    qq = [(1 - p) ** e for e in range(n + 1)]
    total = Fraction(0)
    for mask in range(1 << n):
        outs = [0] * k
        e = 0
        for idx, (i, j) in enumerate(arcs):
            if (mask >> idx) & 1:
                outs[i] |= 1 << j
                e += 1
        total += pp[e] * qq[n - e] * fort_poly(outs, q)
    return total


class TestPi(unittest.TestCase):
    def test_pi_values(self):
        for q in (3, 5, 7):
            self.assertEqual(pi_m(q, 0), 1)
            self.assertEqual(pi_m(q, 1), 0)
            self.assertEqual(pi_m(q, 2), Fraction(1, q - 1))
            for m in range(2, 9):
                self.assertTrue(0 <= pi_m(q, m) <= Fraction(1, q - 1))

    def test_pi_count(self):
        # pi(m) (q-1)^m = #{e in (F_q^*)^m : sum e = 0}, by brute force.
        from itertools import product
        for q in (3, 5):
            for m in range(0, 5):
                cnt = sum(1 for e in product(range(1, q), repeat=m) if sum(e) % q == 0)
                self.assertEqual(Fraction(cnt), pi_m(q, m) * (q - 1) ** m)


class TestFortBound(unittest.TestCase):
    """Proposition 74 and 75 on random sparse matrices, exactly."""

    def test_props_74_75(self):
        rng = random.Random(179)
        cases = [(3, 3, 12), (3, 4, 12), (5, 3, 9)]
        for q, k, reps in cases:
            n = q ** k
            for r in range(reps):
                M = rand_sparse(rng, q, k, (0.3, 0.5, 0.7)[r % 3])
                s, W = frame_stats(M, q)
                EN = Fraction(s, n)
                outs = digraph_of(M)
                pc = Fraction(0)
                for T in range(1 << k):
                    v = V(M, q, T)
                    pc += Fraction(v, q ** popcount(T))
                    if T and not is_fort(outs, T):
                        self.assertEqual(v, 0)
                    self.assertLessEqual(v, (q - 1) ** popcount(T))
                    self.assertLessEqual(v, (q - 1) ** popcount(T) * packing_factor(outs, T, q))
                self.assertEqual(EN, pc)  # a174 pair count
                Phi = fort_poly(outs, q)
                Ps = packing_poly(outs, q)
                self.assertLessEqual(EN, Ps)
                self.assertLessEqual(Ps, Phi)
                # Jensen + Prop 74: 2^H <= Phi, i.e. prod_y N_y <= Phi^(q^k).
                self.assertLessEqual(W * Phi.denominator ** n, Phi.numerator ** n)

    def test_cycle_and_union(self):
        for q in (3, 5):
            a = Fraction(q - 1, q)
            for k in (3, 4, 5, 6):
                cyc = [1 << ((i + 1) % k) for i in range(k)]
                self.assertEqual(fort_poly(cyc, q), 1 + a ** k)
                forts = [T for T in range(1 << k) if is_fort(cyc, T)]
                self.assertEqual(forts, [0, (1 << k) - 1])
            # disjoint union: 3-cycle plus two isolated vertices
            g1 = [1 << 1, 1 << 2, 1 << 0]
            g = g1 + [0, 0]
            self.assertEqual(fort_poly(g, q), fort_poly(g1, q) * (1 + a) ** 2)
            # no arcs at all: the DKSS/Jensen level (2 - 1/q)^k
            self.assertEqual(fort_poly([0] * 4, q), (1 + a) ** 4)


class TestKakeyaCorollary(unittest.TestCase):
    """Corollary 67.1, deterministic part: Lambda(P) <= q log2 Phi_q(G(L))."""

    def test_conjugated_maps(self):
        rng = random.Random(1791)
        for q, k, reps in ((3, 3, 8), (5, 3, 3)):
            n = q ** k
            for r in range(reps):
                A = [rng.randrange(1, q) for _ in range(k)]
                S = [rng.randrange(1, q) for _ in range(k)]
                c = [rng.randrange(q) for _ in range(k)]
                L = rand_sparse(rng, q, k, (0.4, 0.6)[r % 2])
                prodW = 1
                for t in range(q):
                    _, Wt = sum_and_product(fibre_counts(conj_map(A, S, L, c, q, t), q, k))
                    Mt = slice_matrix(A, S, L, q, t)
                    _, WM = frame_stats(Mt, q)
                    self.assertEqual(Wt, WM)  # slice t of P is the frame map of M_t
                    self.assertEqual(digraph_of(Mt), digraph_of(L))
                    prodW *= Wt
                Phi = fort_poly(digraph_of(L), q)
                E = q * n
                self.assertLessEqual(prodW * Phi.denominator ** E, Phi.numerator ** E)


class TestLemma142(unittest.TestCase):
    def test_expected_fort_poly(self):
        for q, k, p in ((3, 3, Fraction(1, 3)), (3, 4, Fraction(1, 2)),
                        (5, 4, Fraction(3, 4)), (3, 4, Fraction(1, 5)), (5, 3, Fraction(1))):
            self.assertEqual(all_digraph_average(q, k, p), expected_fort_poly(q, k, p))


class TestTheorem67(unittest.TestCase):
    def test_ratio_constants(self):
        for q in range(3, 2001, 2):
            self.assertLess(r_head(q), 0.9582)
            self.assertLess(r_mid(q), 0.95)
            self.assertLess(r_tail(q), 0.9570)
        self.assertLess(r_head(3), 0.95812)
        self.assertGreater(r_head(3), 0.95810)

    def test_all_q_analytic(self):
        # tail: exponent H2(13/20) - 1 + phi(1/q), phi(u) = u + 0.65 log2(1 - u) concave,
        # maximised at u* = 1 - 0.65/ln 2.
        ustar = 1 - 0.65 / log(2)

        def phi(u):
            return u + 0.65 * log2(1 - u)
        self.assertLess(2 ** (H2(0.65) - 1 + phi(ustar)), 0.9570)
        for i in range(1, 10001):
            u = i / 30000.0
            self.assertLessEqual(phi(u), phi(ustar) + 1e-12)
        # head: phi1(u) = u + 0.2 log2(1 - u) is increasing on (0, 1/3], so q = 3 is worst.
        self.assertGreater(1 - 0.2 / (log(2) * (1 - 1 / 3)), 0)
        # middle: (1.84 - u) 2^(u - 1) is increasing in u on [0, 1/3].
        self.assertGreater(-1 + (1.84 - 1 / 3) * log(2), 0)

    def test_middle_region_m(self):
        # analytic endpoint values used in the proof (p <= 0.04)
        self.assertGreaterEqual(0.2 * exp(-0.2 * 1.04), 0.16)
        self.assertGreaterEqual((0.65 - 0.04) * exp(-0.65 * 1.04), 0.16)
        self.assertGreaterEqual((2.6 - 0.04) * exp(-2.6 * 1.04), 0.16)
        # direct check of min(h(t1), h(t2)) >= 0.16 on a grid
        for k in range(100, 2001):
            t1 = -(-k // 5)
            t2 = (13 * k) // 20
            for i in range(61):
                c = 1 + 0.05 * i
                p = c / k
                self.assertGreaterEqual(min(h_one(t1, p), h_one(t2, p)), 0.16)

    def test_exact_instances(self):
        for q, k, c in ((3, 100, Fraction(1)), (3, 100, Fraction(4)),
                        (5, 100, Fraction(2)), (3, 100, Fraction(5, 2))):
            E = expected_fort_poly(q, k, c / k)
            self.assertLess(E ** q, 2 ** (k * (q - 1)))  # E Phi < b^k exactly
            bound = (0.9582 ** k + 0.95 ** k + 0.957 ** k) * 2 ** (k * (1 - 1 / q))
            self.assertLessEqual(float(E), bound)

    def test_numerical_window(self):
        grid = [i / 1000.0 for i in range(1, 1000)]
        for c in (0.3, 8.0):
            self.assertLess(max(limit_exponent(3, c, t) for t in grid), 2 / 3 - 0.005)
        self.assertGreater(limit_exponent(3, 0.1, 0.4), 2 / 3)
        self.assertGreater(limit_exponent(3, 12.0, 0.5), 2 / 3)


if __name__ == "__main__":
    unittest.main()
