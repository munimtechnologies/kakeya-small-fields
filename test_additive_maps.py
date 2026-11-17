"""Tests for additive_maps.py (note a157, Theorem 34).

By MV2 of Munim, Inc., 2026-11-17. Researched and written with AI agents working in MV2's name.
Code Apache-2.0.
"""
import math
import random
import unittest

import additive_maps as am


class FieldTests(unittest.TestCase):
    def test_field_axioms_small(self):
        for q in (4, 8, 9, 16, 25, 27, 5):
            F = am.SmallField(q)
            # 1 is the identity, multiplication is commutative, every nonzero element is invertible
            for a in range(q):
                self.assertEqual(F.mul[1][a], a)
                for b in range(q):
                    self.assertEqual(F.mul[a][b], F.mul[b][a])
            for a in range(1, q):
                self.assertIn(1, F.mul[a])

    def test_matches_repo_field_if_present(self):
        try:
            from kakeya_entropy import Field
        except Exception:
            self.skipTest("kakeya_entropy not importable here")
        for q in (4, 8, 9, 16, 25, 27):
            self.assertEqual(am.SmallField(q).mul, Field(q).mul)

    def test_scalar_matrices_multiplicative(self):
        # T_s T_t = T_{st}, so the scalar action is a ring action of F_q
        for q in (4, 9, 8):
            F = am.SmallField(q)
            Ts = am.scalar_matrices(F, 1)
            p = F.p
            for s in range(q):
                for t in range(q):
                    prod = [[sum(Ts[s][i][l] * Ts[t][l][j] for l in range(F.m)) % p
                             for j in range(F.m)] for i in range(F.m)]
                    self.assertEqual(prod, Ts[F.mul[s][t]])


class TheoremTests(unittest.TestCase):
    def test_exhaustive_small(self):
        for q, k in [(2, 2), (3, 2), (4, 1), (8, 1), (9, 1), (25, 1), (4, 2)]:
            r = am.census(q, k)
            print("exhaustive", q, k, "maps", r["maps"], "max sum n_t", r["max_sum"],
                  "bound", r["bound"], "maps at max", r["maps_at_max"])
            self.assertTrue(r["holds"])
            # the bound is attained (by the coordinatewise Frobenius, among others)
            self.assertEqual(r["max_sum"], r["bound"])

    def test_frobenius_attains_bound(self):
        for q, k in [(4, 1), (4, 2), (4, 3), (8, 1), (8, 2), (9, 1), (9, 2), (16, 1), (25, 1),
                     (27, 1), (3, 2), (5, 1)]:
            F = am.SmallField(q)
            dims = am.kernel_dims(am.frobenius_matrix(F, k), am.scalar_matrices(F, k), F.p)
            self.assertEqual(sum(dims), am.bound(q, F.p, k), (q, k, dims))

    def test_random_samples(self):
        for q, k, count in [(4, 3, 300), (8, 2, 200), (9, 2, 200), (16, 1, 300), (27, 1, 300)]:
            r = am.sample(q, k, count, seed=7)
            self.assertTrue(r["holds"], (q, k, r["max_sum"], r["bound"]))

    def test_score_formula_matches_fibres(self):
        rng = random.Random(3)
        for q, k in [(4, 2), (8, 1), (9, 1), (3, 2), (4, 1)]:
            F = am.SmallField(q)
            Ts = am.scalar_matrices(F, k)
            N = F.m * k
            mats = [am.random_matrix(F.p, N, rng) for _ in range(15)] + [am.frobenius_matrix(F, k)]
            for P in mats:
                dims = am.kernel_dims(P, Ts, F.p)
                self.assertAlmostEqual(am.score_by_fibres(P, Ts, F.p),
                                       am.score_formula(q, k, F.p, dims), places=9)

    def test_threshold_comparison(self):
        # p = 2: the largest additive score equals the threshold (a tie, never a win);
        # odd p: it is strictly below the threshold.
        for q, k in [(4, 1), (4, 2), (8, 1), (16, 1), (9, 1), (9, 2), (25, 1), (27, 1), (5, 2)]:
            F = am.SmallField(q)
            best = am.score_formula(q, k, F.p, [am.bound(q, F.p, k)])
            if F.p == 2:
                self.assertTrue(math.isclose(best, am.threshold(q, k)))
            else:
                self.assertLess(best, am.threshold(q, k))

    def test_frobenius_is_threshold_map_for_q4(self):
        # S of the coordinatewise square map on F_4^2 is 96, the q = 4, k = 2 threshold
        F = am.SmallField(4)
        Ts = am.scalar_matrices(F, 2)
        self.assertAlmostEqual(am.score_by_fibres(am.frobenius_matrix(F, 2), Ts, 2), 96.0)


if __name__ == "__main__":
    unittest.main(verbosity=2)
