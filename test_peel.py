# SPDX-License-Identifier: Apache-2.0
"""Tests for peel.py (note a168: Theorem 47, Corollaries 47.1-47.3, Propositions 54-55,
Lemma 122).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a168 (or in the
published notes it cites), so a failure means a bug in the code or an error in a hand
proof. The commit carrying a168 ships only if all of them pass.
"""

import math
import random
import unittest

import peel as P

EPS = 1e-9
PRIMES = [p for p in range(3, 200) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def random_map(q, k, rng):
    return {x: tuple(rng.randrange(q) for _ in range(k)) for x in P.points(q, k)}


def random_quadratic(q, k, rng):
    """A random map of degree <= 2: each coordinate a random quadratic polynomial."""
    mons = [(i, j) for i in range(k) for j in range(i, k)]
    co = [([rng.randrange(q) for _ in mons], [rng.randrange(q) for _ in range(k)],
           rng.randrange(q)) for _ in range(k)]

    def ev(x):
        return tuple((sum(a * x[i] * x[j] for a, (i, j) in zip(Q, mons))
                      + sum(b * xi for b, xi in zip(L, x)) + c) % q for Q, L, c in co)
    return {x: ev(x) for x in P.points(q, k)}


def random_slicing(q, k, rng, affine_g=False):
    while True:
        psi = tuple(rng.randrange(q) for _ in range(k))
        if any(psi):
            break
    while True:
        e = tuple(rng.randrange(q) for _ in range(k))
        if P.dot(psi, e, q) == 1:
            break
    if affine_g:
        a = [rng.randrange(q) for _ in range(k - 1)]
        b = rng.randrange(q)
        g = {u: (P.dot(a, u, q) + b) % q for u in P.points(q, k - 1)}
    else:
        g = {u: rng.randrange(q) for u in P.points(q, k - 1)}
    return psi, e, g


class TestTheorem47(unittest.TestCase):
    """Peeling: Lambda(P) = ell(f) + sum_t H(X|Y_t,f) and, slice by slice and t by t,
    H(X | Y_t, f = z) <= H(U | P'_z(U) + tU). Hence Lambda(P) <= ell(f) + E_z Lambda(P'_z)."""

    def check(self, tab, q, k, psi, e, g):
        f, pi, sigma = P.graph_slicing(q, k, psi, e, g)
        # the slicing is a genuine graph slicing: pi(sigma(z,u)) = u, f(sigma(z,u)) = z
        for z in range(q):
            for u in P.points(q, k - 1):
                x = sigma(z, u)
                self.assertEqual(pi(x), u)
                self.assertEqual(f[x], z)
        L = P.lam(tab, q)
        el = P.ell(tab, q, f)
        ins = P.inslice(tab, q, f)
        self.assertAlmostEqual(L, el + ins, delta=EPS)
        proj = [P.projected(tab, q, k, pi, sigma, z) for z in range(q)]
        for t in range(q):
            for z in range(q):
                self.assertLessEqual(P.slice_entropy(tab, q, t, f, z),
                                     P.h_single(proj[z], q, t) + EPS)
        avg = sum(P.lam(pz, q) for pz in proj) / q
        self.assertLessEqual(ins, avg + EPS)
        self.assertLessEqual(L, el + avg + EPS)
        return el, avg

    def test_random_maps_random_graphs(self):
        rng = random.Random(168)
        for q, k, reps in ((3, 2, 8), (3, 3, 4), (5, 2, 5), (5, 3, 1), (7, 2, 2)):
            for _ in range(reps):
                tab = random_map(q, k, rng)
                psi, e, g = random_slicing(q, k, rng)
                self.check(tab, q, k, psi, e, g)

    def test_quadratic_maps_affine_graphs(self):
        """Corollary 47.3 setting: P quadratic, g affine => every P'_z is quadratic, so
        C_q(k-1) for quadratic maps bounds E_z Lambda(P'_z) (Theorems 38, 43; q odd)."""
        rng = random.Random(1680)
        for q, k, reps in ((3, 2, 4), (3, 3, 3), (5, 2, 3), (5, 3, 2), (3, 4, 1)):
            for _ in range(reps):
                tab = random_quadratic(q, k, rng)
                psi, e, g = random_slicing(q, k, rng, affine_g=True)
                _, avg = self.check(tab, q, k, psi, e, g)
                self.assertLessEqual(avg, (k - 1) * (q - 1) + EPS)


class TestCorollary47_2(unittest.TestCase):
    """For the frame product (x_i^2), slicing by x_1 gives ell = q - 1 and the in-slice
    part (k-1)(q-1): the peeling inequality is an equality there."""

    def test_frame(self):
        for q, k in ((3, 2), (3, 3), (5, 2), (5, 3), (7, 2)):
            tab = P.frame_map(q, k)
            psi = (1,) + (0,) * (k - 1)
            e = psi
            g = {u: 0 for u in P.points(q, k - 1)}
            f, pi, sigma = P.graph_slicing(q, k, psi, e, g)
            self.assertAlmostEqual(P.ell(tab, q, f), q - 1, delta=EPS)
            self.assertAlmostEqual(P.inslice(tab, q, f), (k - 1) * (q - 1), delta=EPS)
            avg = sum(P.lam(P.projected(tab, q, k, pi, sigma, z), q) for z in range(q)) / q
            self.assertAlmostEqual(avg, (k - 1) * (q - 1), delta=EPS)
            self.assertAlmostEqual(P.lam(tab, q), k * (q - 1), delta=EPS)


class TestProposition54(unittest.TestCase):
    """Squaring in F_(q^k): Lambda = q - q^(1-k) and ell(psi) = q - 1 for EVERY psi != 0."""

    def test_squaring(self):
        for q, k in ((3, 2), (5, 2), (7, 2), (3, 3), (5, 3)):
            tab = P.squaring_map(q, k)
            self.assertAlmostEqual(P.lam(tab, q), q - q ** (1 - k), delta=EPS)
            for psi in P.points(q, k):
                if not any(psi):
                    continue
                f = {x: P.dot(psi, x, q) for x in tab}
                self.assertAlmostEqual(P.ell(tab, q, f), q - 1, delta=EPS)

    def test_field_is_field(self):
        # the squaring map's fibres at t are {z, -t-z}: sizes 1 or 2 only
        for q, k in ((3, 2), (5, 3)):
            tab = P.squaring_map(q, k)
            for t in range(q):
                sizes = {}
                for x, y in tab.items():
                    key = tuple((yi + t * xi) % q for yi, xi in zip(y, x))
                    sizes[key] = sizes.get(key, 0) + 1
                self.assertEqual(max(sizes.values()), 2)
                self.assertEqual(sum(1 for s in sizes.values() if s == 1), 1)


class TestProposition55(unittest.TestCase):
    """G_n sliced by tau: Lemma 122 closed forms, ell(tau) <= q - 1, and peeling."""

    def ell_tau(self, q, n):
        tab = P.g_map(q, n)
        f = {x: x[n] for x in tab}
        per_t = [P.h_terms(tab, q, t, f)[1] for t in range(q)]
        return tab, f, per_t

    def test_lemma122_closed_forms(self):
        for q, n in ((3, 2), (3, 3), (5, 2), (5, 3), (7, 2), (7, 3), (11, 2)):
            _, _, per_t = self.ell_tau(q, n)
            cnt = P.n_counts(q, n)
            for t in range(1, q):
                self.assertAlmostEqual(per_t[t], P.ell_t_formula(q, n, cnt), delta=EPS)
            self.assertAlmostEqual(per_t[0], P.ell_0_formula(q, n, cnt), delta=EPS)

    def test_ell_tau_small_cases_brute_force(self):
        """Proposition 55(c): the cases not covered by the estimate."""
        for q, n in ((3, 2), (3, 3), (3, 4), (5, 2)):
            _, _, per_t = self.ell_tau(q, n)
            self.assertLessEqual(sum(per_t), q - 1 + EPS)

    def test_ell_tau_bound(self):
        """Proposition 55(b): the estimate is >= the exact value and <= q - 1."""
        for q, n in ((5, 3), (7, 2), (7, 3), (11, 2), (11, 3)):
            _, _, per_t = self.ell_tau(q, n)
            self.assertLessEqual(sum(per_t), P.ell_tau_bound(q, n) + EPS)
        for q in PRIMES:
            for n in range(2, 11):
                if q == 5 and n == 2:
                    continue
                if q == 3:
                    continue
                self.assertLessEqual(P.ell_tau_bound(q, n), q - 1 - 0.2, (q, n))

    def test_peeling_G3(self):
        """Corollary 55.1: Lambda(G_3) <= ell(tau) + E_z Lambda(P'_z) <= (q-1) + 3(q-1)."""
        for q in (3, 5, 7):
            n = 3
            tab, f, per_t = self.ell_tau(q, n)
            k = n + 1
            psi = (0,) * n + (1,)
            g = {u: 0 for u in P.points(q, k - 1)}
            f2, pi, sigma = P.graph_slicing(q, k, psi, psi, g)
            self.assertEqual(f2, f)
            avg = sum(P.lam(P.projected(tab, q, k, pi, sigma, z), q) for z in range(q)) / q
            self.assertLessEqual(avg, 3 * (q - 1) + EPS)
            self.assertLessEqual(P.lam(tab, q), sum(per_t) + avg + EPS)
            self.assertLessEqual(sum(per_t), q - 1 + EPS)


if __name__ == "__main__":
    unittest.main()
