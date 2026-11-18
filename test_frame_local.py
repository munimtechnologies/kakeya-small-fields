# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Tests for frame_local.py (note a176). Every assertion is a fact proved in notes/a176.md,
checked here exhaustively or on fixed pseudo-random samples. Float comparisons use margins."""
import itertools
import math
import random
import unittest

import frame_local as F

EPS = 1e-9

COEFFS = {
    (3, 1): [(1, 0, 0)],
    (5, 1): [(1, 0, 0)],
    (7, 1): [(3, 2, 5)],
    (3, 2): [(1, 0, 0), (2, 1, 1)],
    (3, 3): [(1, 2, 0), (2, 0, 1), (1, 1, 2)],
    (3, 4): [(1, 0, 0), (2, 1, 0), (1, 2, 1), (2, 2, 2)],
    (5, 2): [(1, 0, 0), (3, 2, 4)],
    (5, 3): [(2, 1, 0), (1, 4, 3), (4, 0, 1)],
    (7, 2): [(1, 3, 0), (5, 0, 2)],
    (7, 3): [(1, 0, 0), (2, 5, 1), (6, 1, 3)],
}


def frame_of(q, k):
    sp = F.Space(q, k)
    return sp, F.frame_map(sp, COEFFS[(q, k)])


def shear(k, q):
    T = [[1 if i == j else 0 for j in range(k)] for i in range(k)]
    Ti = [row[:] for row in T]
    T[0][1] = 1
    Ti[0][1] = q - 1
    return T, Ti


def bound_for(q, k):
    return F.Q3_GAP if q == 3 else F.gamma(q, k)


class TestFrameLocal(unittest.TestCase):

    def test_frame_products_are_extremal(self):
        for (q, k) in COEFFS:
            sp, P = frame_of(q, k)
            self.assertEqual(F.weight(sp, P), 2 ** (k * (q - 1) * q ** k))
            if k >= 2 and q ** k <= 125:
                T, Ti = shear(k, q)
                self.assertEqual(F.conjugate(sp, F.conjugate(sp, P, T, Ti), Ti, T), P)
                Pc = F.conjugate(sp, P, T, Ti)
                self.assertEqual(F.weight(sp, Pc), 2 ** (k * (q - 1) * q ** k))

    def test_closed_form_counts(self):
        # a176 Section 2: N_t and M_t are products of 1 + [u != 0] and 1 + chi(u^2 + delta).
        for (q, k) in [(3, 2), (3, 3), (5, 2), (7, 2), (5, 1)]:
            sp, P = frame_of(q, k)
            op = F.OnePoint(sp, P)
            for x0 in range(sp.N):
                for v in range(sp.N):
                    if v == P[x0]:
                        continue
                    self.assertEqual(op.counts(x0, v),
                                     F.formula_counts(q, COEFFS[(q, k)], sp.digits[x0], sp.digits[v]))

    def test_lemma135_identity(self):
        # S(P) - S(P') = sum_t [h(N_t - 1) - h(M_t)] for every map and every one-point change.
        rng = random.Random(135)
        for (q, k) in [(3, 2), (3, 3), (5, 2)]:
            sp = F.Space(q, k)
            maps = [frame_of(q, k)[1]] + [[rng.randrange(sp.N) for _ in range(sp.N)] for _ in range(2)]
            for P in maps:
                op = F.OnePoint(sp, P)
                S0, W0 = F.score(sp, P), F.weight(sp, P)
                for x0 in range(sp.N):
                    for v in range(sp.N):
                        if v == P[x0]:
                            continue
                        Ns, Ms = op.counts(x0, v)
                        Q = F.apply_changes(P, {x0: v})
                        self.assertAlmostEqual(S0 - F.score(sp, Q), F.gap(Ns, Ms), places=8)
                        W1 = F.weight(sp, Q)
                        self.assertEqual(F.exact_one_point_sign(Ns, Ms), (W1 > W0) - (W1 < W0))

    def test_theorem62_exhaustive_one_point(self):
        # Every one-point change of a frame product strictly lowers Lambda when k >= 2,
        # by at least gamma(q,k) (q >= 5) or 0.64 (q = 3), in units of S = q^k Lambda.
        for (q, k) in [(3, 2), (3, 3), (3, 4), (5, 2), (5, 3), (7, 2)]:
            sp, P = frame_of(q, k)
            op = F.OnePoint(sp, P)
            b = bound_for(q, k)
            self.assertGreater(b, 0)
            for x0 in range(sp.N):
                for v in range(sp.N):
                    if v == P[x0]:
                        continue
                    Ns, Ms = op.counts(x0, v)
                    self.assertEqual(F.exact_one_point_sign(Ns, Ms), -1)
                    self.assertGreaterEqual(F.gap(Ns, Ms), b - EPS)

    def test_theorem62_conjugated_frames(self):
        for (q, k) in [(3, 2), (3, 3), (5, 2)]:
            sp, P = frame_of(q, k)
            T, Ti = shear(k, q)
            Pc = F.conjugate(sp, P, T, Ti)
            op = F.OnePoint(sp, Pc)
            for x0 in range(sp.N):
                for v in range(sp.N):
                    if v != Pc[x0]:
                        self.assertEqual(F.exact_one_point_sign(*op.counts(x0, v)), -1)

    def test_k1_equality_only_at_q3(self):
        # k = 1: gap >= (2 - h(2)/2)(q - 3), so equality can occur only at q = 3, and it does.
        c = 2 - F.h(2) / 2.0
        for q in (3, 5, 7):
            sp, P = frame_of(q, 1)
            op = F.OnePoint(sp, P)
            signs = []
            for x0 in range(q):
                for v in range(q):
                    if v != P[x0]:
                        Ns, Ms = op.counts(x0, v)
                        signs.append(F.exact_one_point_sign(Ns, Ms))
                        self.assertGreaterEqual(F.gap(Ns, Ms), c * (q - 3) - EPS)
            self.assertNotIn(1, signs)
            if q == 3:
                self.assertIn(0, signs)
            else:
                self.assertEqual(set(signs), {-1})
        for q in (3, 5, 7, 11):
            self.assertAlmostEqual(F.min_config_gap(q, 1), c * (q - 3), places=9)

    def test_configuration_enumeration(self):
        # All abstract configurations (a superset of all one-point changes of all frames).
        for k in range(2, 8):
            self.assertGreaterEqual(F.min_config_gap(3, k), F.Q3_GAP)
        self.assertAlmostEqual(F.min_config_gap(3, 2), 2 * (F.h(3) - F.h(2)), places=9)
        for (q, k) in [(5, 2), (5, 3), (5, 4), (7, 2), (7, 3)]:
            self.assertGreaterEqual(F.min_config_gap(q, k), F.gamma(q, k) - EPS)

    def test_q3_k2_minimum_attained(self):
        sp, P = frame_of(3, 2)
        op = F.OnePoint(sp, P)
        m = min(F.gap(*op.counts(x0, v)) for x0 in range(9) for v in range(9) if v != P[x0])
        self.assertAlmostEqual(m, 2 * (F.h(3) - F.h(2)), places=9)

    def test_numeric_lemmas(self):
        # Lemma 137: psi(a)/a strictly decreasing; Lemma 138: h(2^k) - psi(k) <= log2(e)/(2^k - 1).
        for a in range(1, 20):
            self.assertLess(F.psi(a + 1) / (a + 1), F.psi(a) / a)
            self.assertGreater(F.psi(a + 1), F.psi(a))
        for k in range(1, 11):  # small k only: the slack is ~ log2(e)/4^k, keep it above float error
            self.assertLessEqual(F.h(2 ** k) - F.psi(k), F.LOG2E / (2 ** k - 1) + 1e-12)
        for q in (5, 7, 11, 13, 101):
            for k in range(2, 20):
                self.assertLess((q + 1) * F.h(2 ** k), 2 * (q - 1) * F.psi(k))
                self.assertGreater(F.gamma(q, k), 0)
        # Proposition 70 constant: 2 log2(e) ln(5/4) > 0.64.
        self.assertGreater(2 * F.LOG2E * math.log(5 / 4.0), F.Q3_GAP)

    def test_radius_table(self):
        table = {(5, 2): 2, (5, 3): 2, (5, 4): 3, (7, 2): 3, (7, 3): 4}
        for (q, k), s in table.items():
            self.assertEqual(F.radius(q, k), s)

    def test_lemma136_random_maps(self):
        rng = random.Random(136)
        for (q, k) in [(3, 2), (3, 3), (5, 2)]:
            sp = F.Space(q, k)
            for _ in range(150):
                P = [rng.randrange(sp.N) for _ in range(sp.N)]
                s = rng.randint(1, 5)
                pts = rng.sample(range(sp.N), s)
                ch = {}
                for x in pts:
                    v = rng.randrange(sp.N - 1)
                    ch[x] = v if v < P[x] else v + 1
                lhs = F.score(sp, P) - F.score(sp, F.apply_changes(P, ch))
                self.assertGreaterEqual(lhs, F.lemma136_bound(sp, P, ch) - EPS)

    def test_corollary62_two_points_q5_k2(self):
        sp, P = frame_of(5, 2)
        S0 = F.score(sp, P)
        b = 2 * F.gamma(5, 2) - 4
        self.assertGreater(b, 0.3)
        for x in (0, 13):
            for y in range(sp.N):
                if y == x:
                    continue
                for vx in range(sp.N):
                    if vx == P[x]:
                        continue
                    for vy in range(sp.N):
                        if vy == P[y]:
                            continue
                        Q = F.apply_changes(P, {x: vx, y: vy})
                        self.assertGreaterEqual(S0 - F.score(sp, Q), b - EPS)

    def test_corollary62_samples(self):
        rng = random.Random(62)
        for (q, k, s, n) in [(7, 2, 3, 1500), (5, 3, 2, 800), (7, 3, 4, 200)]:
            sp, P = frame_of(q, k)
            S0 = F.score(sp, P)
            b = s * F.gamma(q, k) - 2 * s * (s - 1)
            self.assertGreater(b, 0)
            for _ in range(n):
                ch = {}
                for x in rng.sample(range(sp.N), s):
                    v = rng.randrange(sp.N - 1)
                    ch[x] = v if v < P[x] else v + 1
                self.assertGreaterEqual(S0 - F.score(sp, F.apply_changes(P, ch)), b - EPS)


if __name__ == "__main__":
    unittest.main()
