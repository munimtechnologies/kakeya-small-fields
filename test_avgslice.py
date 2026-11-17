# SPDX-License-Identifier: Apache-2.0
"""Tests for avgslice.py (note a169: Lemmas 123-124, Theorem 48, Corollaries 48.1-48.2,
Proposition 56, Theorem 49).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a169, so a failure
means a bug in the code or an error in a hand proof. The commit carrying a169 ships only
if all of them pass.
"""

import math
import random
import unittest

import avgslice as A

EPS = 1e-9


def random_map(q, k, rng):
    return {x: tuple(rng.randrange(q) for _ in range(k)) for x in A.points(q, k)}


def small_image_map(q, k, rng, size=3):
    vals = [tuple(rng.randrange(q) for _ in range(k)) for _ in range(size)]
    return {x: rng.choice(vals) for x in A.points(q, k)}


def random_quadratic(q, k, rng):
    mons = [(i, j) for i in range(k) for j in range(i, k)]
    co = [([rng.randrange(q) for _ in mons], [rng.randrange(q) for _ in range(k)],
           rng.randrange(q)) for _ in range(k)]

    def ev(x):
        return tuple((sum(a * x[i] * x[j] for a, (i, j) in zip(Q, mons))
                      + sum(b * xi for b, xi in zip(L, x)) + c) % q for Q, L, c in co)
    return {x: ev(x) for x in A.points(q, k)}


def random_affine(q, k, rng):
    M = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]
    return {x: tuple((A.dot(M[i], x, q) + c[i]) % q for i in range(k))
            for x in A.points(q, k)}


def frame_product(q, k):
    return {x: tuple(v * v % q for v in x) for x in A.points(q, k)}


def scalar_map(q, k, a):
    return {x: tuple(a * v % q for v in x) for x in A.points(q, k)}


def sample_maps(q, k, seed):
    rng = random.Random(seed)
    maps = [random_map(q, k, rng), random_map(q, k, rng), small_image_map(q, k, rng),
            random_quadratic(q, k, rng), random_affine(q, k, rng), frame_product(q, k),
            scalar_map(q, k, q - 1)]
    if k == 2:
        maps.append(A.squaring_plane(q, 1 + rng.randrange(q - 1),
                                     (rng.randrange(q), rng.randrange(q))))
    return maps


SIZES = [(3, 2), (5, 2), (7, 2), (3, 3), (5, 3)]


class TestLemma123(unittest.TestCase):
    """Triangle lemma: at a cherry y -t- x -t'- z (t != t'), y and z never collide if x, y, z
    are not collinear, and collide exactly at s = (t - mu t')/(1 - mu) if x - z = mu (x - y).
    Within one fibre (t = t') they collide at t."""

    def test_triangles(self):
        for (q, k) in [(3, 2), (5, 2), (7, 2), (3, 3)]:
            for i, tab in enumerate(sample_maps(q, k, 100 * q + k)):
                with self.subTest(q=q, k=k, map=i):
                    self.assertEqual(A.triangle_violations(tab, q, k), [])

    def test_line_criterion(self):
        """On a line with direction v (k = 2), x and y collide iff nu_v(P(x)) = nu_v(P(y))."""
        for q in (3, 5, 7):
            for i, tab in enumerate(sample_maps(q, 2, 7 * q)):
                col = A.collision_table(tab, q, 2)
                for (x, y), t in col.items():
                    v = ((y[0] - x[0]) % q, (y[1] - x[1]) % q)
                    nu = A.normal(v, q)
                    same = A.dot(nu, tab[x], q) == A.dot(nu, tab[y], q)
                    self.assertEqual(t is not None, same, (q, i, x, y))


class TestLemma124Theorem48(unittest.TestCase):
    """Lemma 124: for every set F of m points, E_psi H(psi(U)) <= (1 - p_k) log2 m.
    Theorem 48: E_psi ell(psi) <= (1 - p_k) Lambda(P). Corollary 48.1: if
    Lambda(P) <= q - q^(1-k) then some linear psi has ell(psi) <= q - 1."""

    def test_fibres_and_maps(self):
        for (q, k) in SIZES:
            p = A.p_k(q, k)
            fs = A.proj_functionals(q, k)
            self.assertEqual(len(fs), (q ** k - 1) // (q - 1))
            for i, tab in enumerate(sample_maps(q, k, 31 * q + k)):
                with self.subTest(q=q, k=k, map=i):
                    fib = A.all_fibres(tab, q, k)
                    for Ft in fib:
                        for F in Ft:
                            if len(F) > 1:
                                self.assertLessEqual(A.avg_slice_entropy(F, q, k),
                                                     (1 - p) * math.log2(len(F)) + EPS)
                    L = A.lam(tab, q, k, fib)
                    ells = [A.ell_lin(tab, q, k, psi, fib) for psi in fs]
                    self.assertLessEqual(sum(ells) / len(ells), (1 - p) * L + EPS)
                    if L <= A.threshold(q, k) + EPS:
                        self.assertLessEqual(min(ells), q - 1 + EPS)

    def test_threshold_formula(self):
        for q in (3, 4, 5, 7, 8, 9, 11, 13):
            for k in (1, 2, 3, 4, 5):
                self.assertAlmostEqual((q - 1) / (1 - A.p_k(q, k)), A.threshold(q, k),
                                       places=9)

    def test_squaring_equality(self):
        """Corollary 48.2 and the equality case: z -> a z^2 + b z on F_(q^2) has only
        fibres of size <= 2, Lambda = q - 1/q = threshold(q, 2), and the average of ell over
        psi is exactly q - 1 (Lemma 124 is an equality for 2-point fibres)."""
        rng = random.Random(5)
        for q in (3, 5, 7, 11):
            for _ in range(2):
                tab = A.squaring_plane(q, 1 + rng.randrange(q - 1),
                                       (rng.randrange(q), rng.randrange(q)))
                fib = A.all_fibres(tab, q, 2)
                self.assertTrue(all(len(F) <= 2 for Ft in fib for F in Ft))
                L = A.lam(tab, q, 2, fib)
                self.assertAlmostEqual(L, q - 1 / q, places=9)
                self.assertAlmostEqual(L, A.threshold(q, 2), places=9)
                fs = A.proj_functionals(q, 2)
                ells = [A.ell_lin(tab, q, 2, psi, fib) for psi in fs]
                self.assertAlmostEqual(sum(ells) / len(ells), q - 1, places=9)
                self.assertLessEqual(min(ells), q - 1 + EPS)


class TestProposition56(unittest.TestCase):
    """Plane decomposition (k = 2): Lambda = ell(nu_v) + Lambda_v for every direction v,
    Lambda_v <= E(c_v - 1) <= q - 1, and sum_v Lambda_v >= Lambda, with equality when every
    fibre is collinear (for example when every fibre has at most 2 points)."""

    def test_decomposition(self):
        for q in (3, 5, 7):
            dirs = A.proj_functionals(q, 2)  # also one vector per direction
            for i, tab in enumerate(sample_maps(q, 2, 11 * q)):
                with self.subTest(q=q, map=i):
                    fib = A.all_fibres(tab, q, 2)
                    L = A.lam(tab, q, 2, fib)
                    tot = 0.0
                    for v in dirs:
                        Lv = A.directional_loss(tab, q, v, fib)
                        tot += Lv
                        e = A.ell_lin(tab, q, 2, A.normal(v, q), fib)
                        self.assertAlmostEqual(e + Lv, L, places=9)
                        c = A.mean_cluster_excess(tab, q, v)
                        self.assertLessEqual(Lv, c + EPS)
                        self.assertLessEqual(c, q - 1 + EPS)
                    self.assertGreaterEqual(tot, L - EPS)
                    if all(len(F) <= 2 for Ft in fib for F in Ft):
                        self.assertAlmostEqual(tot, L, places=9)

    def test_frame_product_strict(self):
        """Frame products have 4-point rectangle fibres, so the inequality is strict."""
        for q in (3, 5, 7):
            tab = frame_product(q, 2)
            fib = A.all_fibres(tab, q, 2)
            L = A.lam(tab, q, 2, fib)
            self.assertAlmostEqual(L, 2 * (q - 1), places=9)
            tot = sum(A.directional_loss(tab, q, v, fib) for v in A.proj_functionals(q, 2))
            self.assertGreater(tot, L + 0.5)


class TestTheorem49(unittest.TestCase):
    """The record slack q log2(2 - 1/q) - (q - 1) is positive, increasing in q, above 0.2 for
    q >= 3, and below its limit 1 - 1/(2 ln 2)."""

    def test_slack(self):
        lim = 1 - 1 / (2 * math.log(2))
        self.assertAlmostEqual(A.record_slack(2), 2 * math.log2(1.5) - 1, places=12)
        prev = A.record_slack(2)
        self.assertGreater(prev, 0.16)
        for q in range(3, 400):
            s = A.record_slack(q)
            self.assertGreater(s, 0.2)
            self.assertLess(s, lim)
            self.assertGreater(s, prev)
            prev = s
        self.assertAlmostEqual(A.record_slack(3), 3 * math.log2(5 / 3) - 2, places=12)
        self.assertTrue(0.2108 < A.record_slack(3) < 0.2110)
        self.assertTrue(0.2399 < A.record_slack(5) < 0.2401)


if __name__ == "__main__":
    unittest.main()
