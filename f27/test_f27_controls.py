# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Controls for f27/f27scan.py (f27/F27.md): the field, the score against an independent
implementation, the symmetries, the coset representatives, the product map (S = 162
exactly) and every F_3-linear map (S <= 81 log2 3)."""
import math
import os
import random
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import f27scan as F
except ImportError:  # pragma: no cover
    import f27scan as F

N = 27


def product_map():
    f = (0, 0, 1)  # the best one-dimensional map: 0 -> 0, 1 -> 0, 2 -> 1
    return [F.to_idx(tuple(f[u] for u in F.to_vec(x))) for x in range(N)]


class TestField(unittest.TestCase):
    def test_a_field_axioms(self):
        A, M = F.ADD, F.MUL
        for x in range(N):
            self.assertEqual(M[1][x], x)
            self.assertEqual(M[0][x], 0)
            for y in range(N):
                self.assertEqual(M[x][y], M[y][x])
                for z in range(N):
                    self.assertEqual(M[x][A[y][z]], A[M[x][y]][M[x][z]])
                    self.assertEqual(M[M[x][y]][z], M[x][M[y][z]])
        for x in range(1, N):
            self.assertEqual(sum(1 for y in range(N) if M[x][y] == 1), 1)

    def test_b_generator_and_powers(self):
        self.assertIsNotNone(F.GEN)
        self.assertEqual(F.order(F.GEN), 26)
        a = 3  # the class of a
        a3 = F.MUL[F.MUL[a][a]][a]
        self.assertEqual(F.ADD[F.ADD[a3][F.MUL[2][a]]][1], 0)  # a^3 + 2a + 1 = 0
        for x in range(1, N):
            self.assertEqual(F.POW[26][x], 1)
            self.assertEqual(F.MUL[F.POW[26][x]][x], x)
        self.assertEqual(len(set(tuple(F.POW[e]) for e in range(1, N))), 26)
        # x -> x^3 is additive (Frobenius), x -> x^2 is not
        for x in range(N):
            for y in range(N):
                self.assertEqual(F.POW[3][F.ADD[x][y]], F.ADD[F.POW[3][x]][F.POW[3][y]])
        self.assertTrue(any(F.POW[2][F.ADD[x][y]] != F.ADD[F.POW[2][x]][F.POW[2][y]]
                            for x in range(N) for y in range(N)))


class TestScore(unittest.TestCase):
    def test_c_score_matches_reference(self):
        rng = random.Random(20261127)
        for _ in range(300):
            P = [rng.randrange(N) for _ in range(N)]
            s = F.score(P)
            self.assertAlmostEqual(s, F.score_reference(P), places=9)
            self.assertAlmostEqual(s, math.log2(F.exact_q(P)), places=7)

    def test_d_product_map_scores_exactly_162(self):
        P = product_map()
        self.assertEqual(F.exact_q(P), 2 ** 162)
        self.assertEqual(F.classify(P), 0)
        self.assertAlmostEqual(F.score(P), 162.0, places=9)

    def test_e_symmetries(self):
        rng = random.Random(7)
        for _ in range(60):
            P = [rng.randrange(N) for _ in range(N)]
            s = F.score(P)
            c = rng.randrange(N)
            self.assertAlmostEqual(F.score([F.ADD[p][c] for p in P]), s, places=9)
            t = rng.randrange(3)
            self.assertAlmostEqual(F.score([F.ADD[p][F.TX[t][x]] for x, p in enumerate(P)]),
                                   s, places=9)
            mu = rng.randrange(1, N)
            mi = [y for y in range(N) if F.MUL[mu][y] == 1][0]
            Q = [F.MUL[mi][P[F.MUL[mu][x]]] for x in range(N)]
            self.assertAlmostEqual(F.score(Q), s, places=9)

    def test_f_conjugation_moves_coefficients(self):
        rng = random.Random(11)
        for _ in range(40):
            e1, e2 = rng.sample(range(1, N), 2)
            c1, c2, mu = rng.randrange(1, N), rng.randrange(1, N), rng.randrange(1, N)
            mi = [y for y in range(N) if F.MUL[mu][y] == 1][0]
            P = [F.ADD[F.COL[e1][c1][x]][F.COL[e2][c2][x]] for x in range(N)]
            Q = [F.MUL[mi][P[F.MUL[mu][x]]] for x in range(N)]
            d1 = F.MUL[c1][F.power(mu, e1 - 1)]
            d2 = F.MUL[c2][F.power(mu, e2 - 1)]
            R = [F.ADD[F.COL[e1][d1][x]][F.COL[e2][d2][x]] for x in range(N)]
            self.assertEqual(Q, R)

    def test_g_coset_representatives_cover(self):
        for e in range(2, N):
            reps = set(F.REPS[e])
            g = math.gcd(e - 1, 26)
            self.assertEqual(len(reps), g)
            for c in F.UNITS:
                self.assertTrue(any(F.MUL[c][F.power(mu, e - 1)] in reps for mu in F.UNITS))

    def test_h_every_linear_map_is_below_81_log2_3(self):
        best = max(F.score(L) for _, L in F.all_linear())
        self.assertAlmostEqual(best, 81 * math.log2(3), places=9)
        self.assertLess(best, 162)

    def test_i_family_counts(self):
        self.assertEqual(len(F.poly_tasks()), 26 + 325 + 2600)
        self.assertGreater(F.expected_poly_count(), 3000000)
        self.assertEqual(len(F.NONLIN), 23)
        # exponents whose base-3 digit sum is at least 3 give maps that are not quadratic
        cubic = [e for e in range(1, N) if sum(F.to_vec(e)) >= 3]
        self.assertEqual(len(cubic), 17)


if __name__ == "__main__":
    unittest.main()
