# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Tests for note a182 (sd3_sticky.py). Every assertion is a proved statement checked on
examples (floating point, tolerance 1e-12), an exact count, or a numerical constant
compared with its stated precision."""

import itertools
import json
import math
import os
import random
import unittest

import sd3_sticky as S

TOL = 1e-12


def _n1_config(pmap, weights):
    return {(x,): ((pmap[x],), weights[x]) for x in range(3)}


def _random_invertible(n, rng):
    vecs = S.f3_vectors(n)
    while True:
        mat = [tuple(rng.randrange(3) for _ in range(n)) for _ in range(n)]
        imgs = {tuple(sum(r * x for r, x in zip(row, v)) % 3 for row in mat) for v in vecs}
        if len(imgs) == len(vecs):
            return mat


class TestConstants(unittest.TestCase):
    def test_identities(self):
        self.assertLess(abs(S.C3 - (3.0 - 3.0 / S.R0)), TOL)
        self.assertLess(abs(S.C_TRI - (3.0 / S.R0 - 1.0)), TOL)
        self.assertLess(abs(S.C3 + S.C_TRI - 2.0), TOL)
        self.assertLess(abs(S.R0 - 1.7259824), 1e-6)
        self.assertLess(abs(S.C_TRI - 0.7381405), 1e-6)
        self.assertGreater(S.C_TRI, 0.5)
        self.assertLess(S.C_TRI, 1.0)
        self.assertGreater(S.U_STAR, 1.0)


class TestLemma148(unittest.TestCase):
    def test_simplex_grid(self):
        steps = 300
        for i in range(steps + 1):
            for j in range(steps + 1 - i):
                p = (i / steps, j / steps, (steps - i - j) / steps)
                self.assertGreater(S.triangle_gap(p), -TOL)

    def test_boundary_formula(self):
        # On the edge p_3 = 0: G = (1 - C_TRI) * h(x).
        for k in range(1, 100):
            x = k / 100.0
            h = S.psi(x) + S.psi(1.0 - x)
            self.assertLess(abs(S.triangle_gap((x, 1.0 - x, 0.0)) - (1.0 - S.C_TRI) * h), TOL)

    def test_equality_points(self):
        self.assertLess(abs(S.phi(0.0)), TOL)
        self.assertLess(abs(S.phi(1.0 / 3.0)), TOL)
        self.assertGreater(S.phi(0.5), 0.0)

    def test_phi_prime_closed_form(self):
        h = 1e-6
        for k in range(2, 99):
            a = k / 200.0
            num = (S.phi(a + h) - S.phi(a - h)) / (2 * h)
            self.assertLess(abs(num - S.phi_prime(a)), 1e-6)

    def test_m_shape(self):
        self.assertEqual(S.m_func(1.0), 0.0)
        self.assertLess(S.m_func(S.U_STAR), 0.0)
        self.assertLess(abs(S.m_func(S.U_STAR) - (-0.118154)), 1e-4)
        self.assertLess(abs(S.U_STAR - 2.818842), 1e-5)
        grid = [S.U_STAR * k / 400.0 for k in range(1, 401)]
        for u, v in zip(grid, grid[1:]):
            self.assertGreater(S.m_func(u), S.m_func(v))           # decreasing
        grid = [S.U_STAR + k / 4.0 for k in range(0, 800)]
        for u, v in zip(grid, grid[1:]):
            self.assertLess(S.m_func(u), S.m_func(v))              # increasing
        self.assertGreater(S.m_func(100.0), 0.0)

    def test_root_and_sign_pattern(self):
        u1 = S.u_root()
        self.assertGreater(u1, S.U_STAR)
        self.assertLess(abs(S.m_func(u1)), 1e-9)
        self.assertLess(abs(u1 - 9.703), 0.005)
        a1 = 1.0 / (u1 + 2.0)
        for k in range(1, 1000):
            a = k / 2000.0
            if abs(a - a1) < 1e-3 or abs(a - 1.0 / 3.0) < 1e-3:
                continue
            d = S.phi_prime(a)
            if a < a1:
                self.assertGreater(d, 0.0)
            elif a < 1.0 / 3.0:
                self.assertLess(d, 0.0)
            else:
                self.assertGreater(d, 0.0)

    def test_phi_nonnegative(self):
        for k in range(0, 1001):
            self.assertGreater(S.phi(k / 2000.0), -TOL)


class TestTheorem70(unittest.TestCase):
    def test_merge_structure(self):
        tri = 0
        for pmap in itertools.product(range(3), repeat=3):
            merges = S.n1_merge_slices(pmap)
            for ts in merges:
                self.assertEqual(len(ts), 1)                     # each pair: exactly one slice
            kinds = {ts[0] for ts in merges}
            self.assertIn(len(kinds), (1, 3))                    # collinear or triangle
            if len(kinds) == 3:
                tri += 1
        self.assertEqual(tri, 18)

    def test_all_maps_all_laws(self):
        rng = random.Random(182)
        laws = [(1.0, 0.0, 0.0), (0.5, 0.5, 0.0), (0.2, 0.0, 0.8), (1 / 3, 1 / 3, 1 / 3)]
        laws += [tuple(rng.random() ** 2 for _ in range(3)) for _ in range(30)]
        for pmap in itertools.product(range(3), repeat=3):
            for w in laws:
                self.assertGreater(S.r3_slack(_n1_config(pmap, w)), -TOL)

    def test_ruzsa_equality(self):
        for n in (1, 2, 3):
            conf = S.ruzsa_product(n)
            self.assertTrue(S.is_triangular(conf))
            self.assertLess(abs(S.r3_slack(conf)), 1e-11)


class TestTheorem71(unittest.TestCase):
    def test_random_triangular(self):
        rng = random.Random(71)
        for n in (1, 2, 3):
            for zp in (0.0, 0.4, 0.8):
                for _ in range(15):
                    conf = S.random_triangular(n, rng, zp)
                    self.assertTrue(S.is_triangular(conf))
                    hd, lost = S.r3_terms(conf)
                    lost2, mid = S.chain_terms(conf)
                    self.assertLess(abs(lost - lost2), 1e-12)
                    self.assertLessEqual(lost, mid + TOL)
                    self.assertLessEqual(mid, S.C3 * hd + TOL)
                    self.assertGreater(S.r3_slack(conf), -TOL)

    def test_change_of_basis(self):
        rng = random.Random(72)
        for n in (2, 3):
            for _ in range(10):
                conf = S.random_triangular(n, rng, 0.3)
                mat = _random_invertible(n, rng)
                moved = S.apply_linear(conf, mat)
                self.assertLess(abs(S.r3_slack(moved) - S.r3_slack(conf)), 1e-10)
                self.assertGreater(S.r3_slack(moved), -TOL)

    def test_triangular_has_invariant_functional(self):
        rng = random.Random(73)
        for _ in range(10):
            conf = S.random_triangular(2, rng)
            self.assertIn((1, 0), S.invariant_functionals(conf))
        self.assertEqual(sorted(S.invariant_functionals(S.ruzsa_product(2))),
                         [(0, 1), (1, 0)])


class TestProposition77(unittest.TestCase):
    def test_defect_bound_random_maps(self):
        rng = random.Random(77)
        for n in (1, 2, 3):
            for zp in (0.0, 0.5):
                for _ in range(15):
                    conf = S.random_map_config(n, rng, zp)
                    hd, lost = S.r3_terms(conf)
                    self.assertLessEqual(lost, S.C3 * hd + 3.0 * S.defect_terms(conf) + TOL)


class TestCounts(unittest.TestCase):
    def test_triple_intersections(self):
        self.assertEqual(S.pair_maps_invariant_count(1, 1), 27)
        self.assertEqual(S.pair_maps_invariant_count(1, 2), 27)

    def test_reducible_count(self):
        self.assertEqual(S.reducible_count_f3_2(), 2121471)
        self.assertEqual(9 ** 9, 387420489)


class TestStickyKakeya(unittest.TestCase):
    def test_binary_kakeya_is_triangular(self):
        for n in (1, 2, 3, 4):
            pts = S.binary_kakeya(n)
            self.assertEqual(len(pts), 2 ** (n + 1) - 1)
            conf = {}
            for d in S.f3_vectors(n):
                if not any(d):
                    continue
                b = tuple((x * x) % 3 for x in d)
                for t in range(3):
                    self.assertIn(S.slice_value(b, d, t), pts)
                conf[d] = (b, 1.0)
            self.assertTrue(S.is_triangular(conf))
            self.assertGreater(S.r3_slack(conf), -TOL)
            # Corollary 71.3: |K| >= (3^n - 1)^(1/R0).
            self.assertGreaterEqual(len(pts), (3 ** n - 1) ** (1.0 / S.R0))


class TestResultsFile(unittest.TestCase):
    def test_numbers(self):
        path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "a182.json")
        if not os.path.exists(path):
            self.skipTest("results/a182.json not present next to the tests")
        with open(path) as fh:
            res = json.load(fh)
        self.assertLess(abs(res["R0"] - S.R0), 1e-6)
        self.assertLess(abs(res["C3"] - S.C3), 1e-6)
        self.assertLess(abs(res["C_TRI"] - S.C_TRI), 1e-6)
        self.assertLess(abs(res["u_star"] - S.U_STAR), 1e-5)
        self.assertLess(abs(res["M_at_u_star"] - S.m_func(S.U_STAR)), 1e-4)
        u1 = S.u_root()
        self.assertLess(abs(res["u1"] - u1), 0.005)
        self.assertLess(abs(res["a1"] - 1.0 / (u1 + 2.0)), 1e-4)
        self.assertEqual(res["triangle_maps_of_F3"], 18)
        self.assertEqual(res["affine_maps_of_F3"], 9)
        self.assertEqual(res["reducible_maps_F3_2"], S.reducible_count_f3_2())
        self.assertEqual(res["all_maps_F3_2"], 9 ** 9)
        self.assertLess(abs(res["reducible_fraction_F3_2"]
                            - S.reducible_count_f3_2() / 9 ** 9), 1e-8)
        b = {row["name"]: row["value"] for row in res["kakeya_bases"]}
        self.assertLess(abs(b["general_lower_a180"] - 3 ** (6.0 / 11.0)), 2e-5)
        self.assertLess(abs(b["general_lower_with_farnamfar"] - 3 ** (1.0 / 1.8263483657)), 2e-5)
        self.assertLess(abs(b["general_upper_klss"] - (27.0 / 4.0) ** (1.0 / 3.0)), 2e-5)
        self.assertLess(abs(b["sticky_lower_a182"] - 3 ** (1.0 / S.R0)), 2e-5)
        self.assertEqual(b["sticky_upper_binary"], 2.0)
        sd = {row["name"]: row["value"] for row in res["sum_difference_constants"]}
        self.assertLess(abs(sd["ruzsa_R0_exact_for_triangular_F3"] - S.R0), 2e-6)
        self.assertLess(abs(sd["lemm_reals_lower"] - 1.77898), 1e-9)
        self.assertLess(abs(sd["farnamfar_upper"] - 1.8263483657), 1e-9)
        self.assertLess(abs(sd["katz_tao_upper"] - 11.0 / 6.0), 2e-6)


if __name__ == "__main__":
    unittest.main()
