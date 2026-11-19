# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
"""Tests for sdz.py: only facts checked by hand (see notes/prereg-sdz.md)."""

import math
import unittest

import sdz


def one_d(pairs):
    return [((x,), (y,)) for x, y in pairs]


class TestSdz(unittest.TestCase):
    def test_staircase_is_lemm(self):
        pts = sdz.staircase(-1, 5)
        want = one_d([(0, 1), (1, 1), (1, 0), (2, 0), (2, -1), (3, -1), (3, -2)])
        self.assertEqual(pts, want)

    def test_injectivity_enforced(self):
        with self.assertRaises(ValueError):
            sdz.Support(one_d([(0, 0), (1, 1)]))
        with self.assertRaises(ValueError):
            sdz.smap_points({(0,): (1,)})

    def test_smap_points(self):
        keys, pts = sdz.smap_points({(-1,): (1,), (0,): (2,), (3, ): (1,)})
        self.assertEqual(keys, [(-1,), (0,), (3,)])
        self.assertEqual(pts, one_d([(0, 1), (1, 1), (2, -1)]))

    def test_ruzsa(self):
        sup = sdz.Support(one_d([(0, 1), (1, 0), (1, 1)]))
        H, hx, hy, hs = sdz.entropies(sup, [1 / 3.0] * 3)
        self.assertAlmostEqual(H, math.log(3.0), places=12)
        h13 = math.log(3.0) - (2.0 / 3.0) * math.log(2.0)
        for h in (hx, hy, hs):
            self.assertAlmostEqual(h, h13, places=12)
        a, a_s = sdz.ratio_pair(H, hx, hy, hs)
        self.assertAlmostEqual(a, sdz.RUZSA, places=12)
        self.assertAlmostEqual(a_s, sdz.RUZSA, places=12)
        self.assertAlmostEqual(sdz.RUZSA, 1.7259824578787, places=10)

    def test_lemm_printed_weights(self):
        sup = sdz.Support(sdz.staircase(-1, 5))
        P = sdz.lemm_law()
        self.assertAlmostEqual(sum(P), 1.0, places=12)
        H, hx, hy, hs = sdz.entropies(sup, P)
        self.assertLess(abs(H - 1.22384), 5e-4)
        self.assertLess(abs(hx - 0.68795), 5e-4)
        self.assertAlmostEqual(hx, hy, places=12)
        a, a_s = sdz.ratio_pair(H, hx, hy, hs)
        self.assertGreater(a, 1.7788)
        self.assertLess(a, 1.7792)

    def test_product_additivity(self):
        sa = sdz.Support(one_d([(0, 1), (1, 0), (1, 1)]))
        sb = sdz.Support(one_d([(0, 1), (1, 0), (1, 1), (2, 0)]))
        pa = [0.2, 0.3, 0.5]
        pb = [0.1, 0.2, 0.3, 0.4]
        sp = sdz.product_support(sa, sb)
        pp = sdz.product_law(pa, pb)
        ea = sdz.entropies(sa, pa)
        eb = sdz.entropies(sb, pb)
        ep = sdz.entropies(sp, pp)
        for k in range(4):
            self.assertAlmostEqual(ep[k], ea[k] + eb[k], places=12)

    def test_mm_monotone(self):
        sup = sdz.Support(sdz.staircase(-2, 6))
        P = [1.0 / sup.n] * sup.n
        for mu in (0.0, 0.25, 0.7):
            r = sdz.ratio_mu(sup, P, mu)
            Q = P
            for _ in range(60):
                Q = sdz.mm(sup, Q, mu, 1)
                r2 = sdz.ratio_mu(sup, Q, mu)
                self.assertGreaterEqual(r2, r - 1e-12)
                r = r2

    def test_verify_matches_float(self):
        sup = sdz.Support(sdz.staircase(-1, 5))
        P = sdz.lemm_law()
        H, hx, hy, hs = sdz.entropies(sup, P)
        a, a_s = sdz.ratio_pair(H, hx, hy, hs)
        va, vs = sdz.verify(sup, P)
        self.assertLess(abs(float(va) - a), 1e-12)
        self.assertLess(abs(float(vs) - a_s), 1e-12)

    def test_center(self):
        P = [0.1, 0.2, 0.3, 0.4]
        C = [[(a + 1) * (b - 2) + a * a for b in range(4)] for a in range(4)]
        D = sdz.center(P, C)
        for a in range(4):
            self.assertAlmostEqual(sum(P[b] * D[a][b] for b in range(4)), 0.0, places=12)
        for b in range(4):
            self.assertAlmostEqual(sum(P[a] * D[a][b] for a in range(4)), 0.0, places=12)

    def test_tensor_parity_eigenvalue_one(self):
        # With all weight on S = X + Y, T = A_S (x) A_S is a projection whose range
        # (parity (x) parity on the staircase) is nonzero: top eigenvalue exactly 1.
        sup = sdz.Support(sdz.staircase(-1, 5))
        r = sdz.tensor_lambda(sup, sdz.lemm_law(), 1.0, iters=3, seed=3)
        self.assertAlmostEqual(r["rayleigh"], 1.0, places=9)

    def test_tensor_bounds(self):
        sup = sdz.Support(sdz.staircase(-1, 5))
        r = sdz.tensor_lambda(sup, sdz.lemm_law(), 0.25, iters=50, seed=1)
        self.assertGreaterEqual(r["rayleigh"], -1e-12)
        self.assertLessEqual(r["rayleigh"], 1.0 + 1e-9)
        for p in r["parts"]:
            self.assertGreaterEqual(p, -1e-12)
            self.assertLessEqual(p, 1.0 + 1e-9)


if __name__ == "__main__":
    unittest.main()
