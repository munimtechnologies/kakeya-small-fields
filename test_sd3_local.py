# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Tests for note a181 (sd3_local.py, sd3_search.py). Every assertion is a proved fact
checked exactly, or a numerical value compared with its stated precision."""

import json
import math
import os
import random
import unittest
from fractions import Fraction

import sd3_local as L
import sd3_search as S


def _mean_zero(vals):
    m = sum(vals.values(), Fraction(0)) / len(vals)
    return {k: v - m for k, v in vals.items()}


class TestRuzsaProduct(unittest.TestCase):
    def test_ratio_is_r0(self):
        self.assertLess(abs(L.R0 - 1.725982), 1e-6)
        for n in (1, 2, 3):
            hd, hs, ravg, rmax = L.ratios(L.ruzsa_product(n))
            self.assertLess(abs(hd - n * L.LOG3), 1e-12)
            for h in hs:
                self.assertLess(abs(h - n * L.H_STAR), 1e-12)
            self.assertLess(abs(ravg - L.R0), 1e-12)
            self.assertLess(abs(rmax - L.R0), 1e-12)

    def test_is_sum_difference_instance(self):
        # X = Y_1, Y = Y_0: X - Y = d and X + Y = -Y_2 in F_3^n.
        for d, (b, _) in L.ruzsa_product(2).items():
            y0, y1, y2 = (L.slice_value(b, d, t) for t in range(3))
            self.assertEqual(tuple((p - q) % 3 for p, q in zip(y1, y0)), d)
            self.assertEqual(tuple((p + q) % 3 for p, q in zip(y1, y0)),
                             tuple((-r) % 3 for r in y2))

    def test_first_order_cancellation(self):
        # Lemma 145: prod_t P(Y_t = Y_t(d)) = (4/27)^n for every direction d.
        for n in (1, 2, 3):
            conf = L.ruzsa_product(n)
            for d in conf:
                self.assertEqual(L.slice_product(conf, d), Fraction(4, 27) ** n)


class TestFrameBound(unittest.TestCase):
    def test_gram(self):
        self.assertEqual(L.gram_lambda_max(1), Fraction(3, 2))
        self.assertEqual(L.gram_lambda_max(2), Fraction(3, 2))
        self.assertEqual(L.gram_lambda_max(3), Fraction(9, 8))
        for s in range(3, 61):
            self.assertLess(L.gram_lambda_max(s), Fraction(3, 2))

    def test_frame_bound_exact(self):
        # Lemma 144: sum_t E[E[f|Y_t]^2] <= (3/2) E[f^2], with equality when n = 1.
        rng = random.Random(181)
        for n in (1, 2, 3):
            dirs = L.f3_vectors(n)
            for _ in range(12):
                f = _mean_zero({d: Fraction(rng.randint(-5, 5)) for d in dirs})
                ef2, tot = L.frame_quantities(n, f)
                self.assertLessEqual(2 * tot, 3 * ef2)
                if n == 1:
                    self.assertEqual(2 * tot, 3 * ef2)

    def test_frame_bound_tight_n2(self):
        # f = sum_t e_t (x) e_t attains 3/2 at n = 2.
        e = {t: {x: (Fraction(2, 3) if x == t else Fraction(-1, 3)) for x in range(3)}
             for t in range(3)}
        f = {d: sum(e[t][d[0]] * e[t][d[1]] for t in range(3)) for d in L.f3_vectors(2)}
        ef2, tot = L.frame_quantities(2, f)
        self.assertGreater(ef2, 0)
        self.assertEqual(2 * tot, 3 * ef2)


class TestLocalOptimality(unittest.TestCase):
    def test_reweighting_lowers_ratio(self):
        rng = random.Random(7)
        for n in (1, 2):
            base = L.ruzsa_product(n)
            for _ in range(6):
                raw = {d: rng.uniform(-1.0, 1.0) for d in base}
                m = sum(raw.values()) / len(raw)
                conf = {d: (b, float(w) * (1.0 + 1e-3 * (raw[d] - m)))
                        for d, (b, w) in base.items()}
                _, _, ravg, rmax = L.ratios(conf)
                self.assertLess(ravg, L.R0)
                self.assertLess(rmax, L.R0)

    def test_n1_triangle_grid(self):
        # Remark 69.4 (numerical only, not a proof): on F_3 the triangle law p gives
        # H(p) <= (R0/3) sum_i h(p_i), equivalently sum_i psi(1-p_i) - k psi(p_i) >= 0.
        def psi(x):
            return 0.0 if x <= 0 else -x * math.log(x)
        k = math.log(9.0 / 4.0) / math.log(3.0)
        steps = 240
        for i in range(steps + 1):
            for j in range(steps + 1 - i):
                p = (i / steps, j / steps, (steps - i - j) / steps)
                val = sum(psi(1.0 - x) - k * psi(x) for x in p)
                self.assertGreater(val, -1e-12)

    def test_one_join(self):
        # Lemma 146, exhaustively.
        for n, big_n in ((1, 2), (1, 3), (2, 3)):
            self.assertEqual(L.max_joins(n, big_n), 1)

    def test_new_point_lowers_ratio(self):
        for eps in (1e-2, 1e-3, 1e-6):
            conf = {d: (b, float(w) * (1.0 - eps))
                    for d, (b, w) in L.embed(L.ruzsa_product(1), 1).items()}
            conf[(0, 1)] = ((0, 0), eps)
            _, _, ravg, rmax = L.ratios(conf)
            self.assertLess(ravg, L.R0)
            self.assertLess(rmax, L.R0)


class TestCharacteristicZeroContrast(unittest.TestCase):
    def test_lemm4_collapses_in_exponent_3(self):
        self.assertEqual(L.lemm4_collapses(1), (3, True))
        self.assertEqual(L.lemm4_collapses(2), (9, True))

    def test_z_perturbation_beats_ruzsa(self):
        tri = [(0, 1), (1, 0), (1, 1)]
        self.assertEqual(L.z_joins((2, 0), tri), 2)
        self.assertEqual(L.z_joins((0, 2), tri), 2)
        self.assertLess(abs(L.z_ratio(L.z_config(0.0)) - L.R0), 1e-12)
        r = L.z_ratio(L.z_config(1e-4))
        self.assertGreater(r, L.R0 + 5e-5)
        self.assertLess(abs(r - 1.726068), 2e-6)


class TestSearch(unittest.TestCase):
    def test_cccp_monotone(self):
        rng = random.Random(3)
        dirs = S.f3_vectors(2)
        for _ in range(3):
            P = S.random_map(2, rng)
            mu = S.starts(dirs, rng, 2)[1]
            last = S.evaluate(P, mu)[0]
            for _ in range(40):
                mu = S.cccp_step(P, mu)
                cur = S.evaluate(P, mu)[0]
                self.assertGreaterEqual(cur, last - 1e-12)
                last = cur

    def test_cccp_returns_to_ruzsa(self):
        P = {(x,): ((x * x) % 3,) for x in range(3)}
        mu = S.cccp(P, {(0,): 0.45, (1,): 0.32, (2,): 0.23}, iters=1000)
        for v in mu.values():
            self.assertLess(abs(v - 1.0 / 3.0), 1e-9)
        self.assertLess(abs(S.evaluate(P, mu)[0]), 1e-12)

    def test_search_runs(self):
        res = S.search(2, minutes=0.02, seed=5, iters=20, restarts=2, keep=3)
        self.assertGreaterEqual(res["maps_tried"], 1)
        self.assertLessEqual(len(res["best"]), 3)


class TestResultsFile(unittest.TestCase):
    def test_numbers(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "a181.json")
        if not os.path.exists(path):
            self.skipTest("results/a181.json not present next to the tests")
        with open(path) as fh:
            res = json.load(fh)
        self.assertLess(abs(res["R0_ruzsa_ratio"] - L.R0), 1e-6)
        expect = [1.8, 3 ** (6.0 / 11.0), 3 ** (1.0 / 1.8263483657), (27.0 / 4.0) ** (1.0 / 3.0)]
        for row, val in zip(res["beta3_bounds"], expect):
            self.assertLess(abs(row["value"] - val), 2e-5)
        sd = [L.R0, 1.77898, 1.8263483657, 11.0 / 6.0]
        for row, val in zip(res["sum_difference_constants"], sd):
            self.assertLess(abs(row["value"] - val), 2e-6)
        for row in res["gram_lambda_max"]:
            self.assertEqual(Fraction(row["value"]), L.gram_lambda_max(row["s"]))
        self.assertLess(abs(res["retention_needed_to_beat_ruzsa"] - 1.0 / L.R0), 1e-6)
        self.assertLess(abs(res["reweighting_margin_1_minus_R0_over_2"] - (1 - L.R0 / 2)), 1e-6)
        self.assertLess(abs(res["new_point_margin_2R0_over_3_minus_1"] - L.KAPPA), 1e-6)
        self.assertEqual(res["frame_retention_bound"], 0.5)
        z = {row["eps"]: row["ratio"] for row in res["z_perturbation"]}
        for eps, val in z.items():
            self.assertLess(abs(L.z_ratio(L.z_config(eps)) - val), 2e-6)


if __name__ == "__main__":
    unittest.main()
