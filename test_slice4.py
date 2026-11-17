# SPDX-License-Identifier: Apache-2.0
"""Tests for slice4.py (note a167: Propositions 52-53, Theorems 44-46, Lemmas 120-121).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a167 (or a numerical
inequality used in a proof there), so a failure means a bug in the code or an error in a
hand proof. The commit carrying a167 ships only if all of them pass.
"""

import math
import random
import unittest
from fractions import Fraction

import slice4 as s4

PRIMES = [p for p in range(3, 200) if all(p % d for d in range(2, int(p ** 0.5) + 1))]


def g_quadratic(q, n):
    """G_n written as Q + L + c in the coefficient format of slice4.random_quadratic."""
    k = n + 1
    A = {(i, j, l): 0 for i in range(k) for j in range(k) for l in range(j, k)}
    for i in range(n):
        A[(i, i, n)] = 1          # Q_i = w_i * tau
    for j in range(n):
        A[(n, j, j)] = 1          # Q_n = w_1^2 + ... + w_n^2
    return A, [[0] * k for _ in range(k)], [0] * k


class TestLemma120(unittest.TestCase):
    """N(0) and sum_c N(c)^2 for Phi = sum of squares."""

    def test_counts(self):
        for q in (3, 5, 7, 11):
            for n in (1, 2, 3, 4):
                if q ** n > 20000:
                    continue
                cnt = s4.n_counts(q, n)
                self.assertEqual(cnt[0], s4.n_zero(q, n), (q, n))
                self.assertEqual(sum(v * v for v in cnt.values()), s4.sum_N_squared(q, n), (q, n))


class TestProp52And53(unittest.TestCase):
    """Pibar = (q-1) E_y e(R_y + L) = q^(1-k) (Sigma - q^k) for every degree-2 map (q odd)."""

    def check(self, A, L, c, q, k):
        tab = s4.table_of(s4.quad_eval(A, L, c, q, k), q, k)
        pb = s4.pibar(tab, q, k)
        self.assertEqual(pb, (q - 1) * s4.mean_eigendirections(A, L, q, k))
        self.assertEqual(pb, Fraction(s4.dual_sigma(A, L, q, k) - q ** k, q ** (k - 1)))

    def test_random(self):
        rng = random.Random(167)
        for q, k, reps in ((3, 2, 6), (3, 3, 5), (3, 4, 2), (5, 2, 3), (5, 3, 2)):
            for _ in range(reps):
                A, L, c = s4.random_quadratic(q, k, rng)
                self.check(A, L, c, q, k)

    def test_G_as_quadratic(self):
        for q, n in ((3, 2), (3, 3), (5, 2)):
            A, L, c = g_quadratic(q, n)
            k = n + 1
            self.assertEqual(s4.table_of(s4.quad_eval(A, L, c, q, k), q, k),
                             s4.table_of(s4.g_map(q, n), q, k))
            self.check(A, L, c, q, k)


class TestIrreducible(unittest.TestCase):
    """Theorem 44(a): G_n respects no nonzero proper subspace (n >= 1); the spin factor
    map neither (n >= 2). Control: the frame product respects exactly the 2^k - 2
    coordinate subspaces."""

    def test_subspace_count(self):
        self.assertEqual(sum(1 for _ in s4.subspaces(3, 4)), 40 + 130 + 40)
        self.assertEqual(sum(1 for _ in s4.subspaces(5, 3)), 31 + 31)

    def test_frame_control(self):
        tab = s4.table_of(s4.frame_map(3, 4), 3, 4)
        self.assertEqual(len(s4.respected_subspaces(tab, 3, 4)), 14)

    def test_G(self):
        for q, n in ((3, 1), (5, 1), (3, 2), (5, 2), (3, 3)):
            tab = s4.table_of(s4.g_map(q, n), q, n + 1)
            self.assertEqual(s4.respected_subspaces(tab, q, n + 1), [], (q, n))

    def test_spin(self):
        for q, n in ((3, 2), (5, 2), (3, 3)):
            tab = s4.table_of(s4.spin_map(q, n), q, n + 1)
            self.assertEqual(s4.respected_subspaces(tab, q, n + 1), [], (q, n))


class TestPiDirections(unittest.TestCase):
    """Theorem 44(b): Pi_v = (q-1) q if v has tau-coordinate != 0, else (q-1) q^n."""

    def test_classification(self):
        for q, n in ((3, 2), (3, 3), (5, 2), (5, 3)):
            k = n + 1
            tab = s4.table_of(s4.g_map(q, n), q, k)
            total = 0
            for v in s4.proj_points(q, k):
                pv = s4.pi_direction(tab, q, v)
                want = (q - 1) * q if v[n] else (q - 1) * q ** n
                self.assertEqual(pv, want, (q, n, v))
                total += pv
            self.assertEqual(Fraction(total, q ** k), s4.pibar(tab, q, k))


class TestPibar(unittest.TestCase):
    """Theorem 44(c): Pibar(G_n) = (q-1) + (q^n - 1)/q; the spin factor adds
    (q-1)^2 N(1/2) / q^n."""

    def test_G(self):
        for q, n in ((3, 1), (3, 2), (3, 3), (3, 4), (5, 2), (5, 3), (7, 3), (11, 3)):
            tab = s4.table_of(s4.g_map(q, n), q, n + 1)
            self.assertEqual(s4.pibar(tab, q, n + 1), s4.pibar_G(q, n), (q, n))

    def test_spin(self):
        for q, n in ((3, 2), (3, 3), (5, 2), (5, 3)):
            tab = s4.table_of(s4.spin_map(q, n), q, n + 1)
            half = s4.inv(2, q)
            extra = Fraction((q - 1) ** 2 * s4.n_counts(q, n)[half], q ** n)
            self.assertEqual(s4.pibar(tab, q, n + 1), s4.pibar_G(q, n) + extra, (q, n))


class TestJensenFails(unittest.TestCase):
    """Theorem 44(d): Q_4 fails for G_3 exactly when q >= 11 (odd primes < 200), and Q_(n+1)
    fails for G_n whenever q^(n-2) >= 2^(n+1)."""

    def test_k4(self):
        for q in PRIMES:
            fails = float(s4.pibar_G(q, 3)) > s4.jensen_threshold(q, 4)
            self.assertEqual(fails, q >= 11, q)
        for q in (11, 13):
            self.assertGreater(s4.jensen_bound(s4.pibar_G(q, 3), q), 4 * (q - 1) + 0.5)
        for q in (3, 5, 7):
            self.assertLess(s4.jensen_bound(s4.pibar_G(q, 3), q), 4 * (q - 1))

    def test_sufficient_condition(self):
        for q in PRIMES[:15]:
            for n in range(3, 11):
                if q ** (n - 2) >= 2 ** (n + 1):
                    self.assertGreater(float(s4.pibar_G(q, n)), q * 2 ** (n + 1))
                    self.assertGreater(float(s4.pibar_G(q, n)), s4.jensen_threshold(q, n + 1))

    def test_k4_large_q_algebra(self):
        # (q-1)(q+1)^2 > 15 q^2 for q >= 17, and 2^(4(q-1)/q) - 1 < 15.
        for q in range(17, 2000, 2):
            self.assertGreater((q - 1) * (q + 1) ** 2, 15 * q * q)


class TestSlicedJensen(unittest.TestCase):
    """Theorem 45: Lambda <= sliced bound, for EVERY map and EVERY slicing."""

    def test_random_maps(self):
        rng = random.Random(45)
        for q, k, reps in ((3, 2, 30), (3, 3, 6), (5, 2, 8)):
            pts = s4.points(q, k)
            for _ in range(reps):
                tab = {x: tuple(rng.randrange(q) for _ in range(k)) for x in pts}
                lam = s4.lam(tab, q, k)
                for nz in (1, 2, 3, q):
                    lab = {x: rng.randrange(nz) for x in pts}
                    self.assertLessEqual(lam, s4.sliced_bound(tab, q, k, lab.__getitem__) + 1e-9)
                # identity slicing = per-t Jensen; constant slicing = per-t Jensen as well
                self.assertLessEqual(lam, s4.sliced_bound(tab, q, k, lambda x: x) + 1e-9)

    def test_random_quadratic(self):
        rng = random.Random(46)
        for q, k in ((3, 3), (3, 4), (5, 3)):
            A, L, c = s4.random_quadratic(q, k, rng)
            tab = s4.table_of(s4.quad_eval(A, L, c, q, k), q, k)
            lam = s4.lam(tab, q, k)
            for i in range(k):
                self.assertLessEqual(lam, s4.sliced_bound(tab, q, k, lambda x, i=i: x[i]) + 1e-9)


class TestLemma121(unittest.TestCase):
    """Fibre structure of G_n sliced by tau: D_t in closed form; in-slice collisions only in
    the slice tau = -t, where 1 + p = q^(n-1) + 1 - 1/q."""

    def test_structure(self):
        for q, n in ((3, 2), (5, 2), (3, 3), (5, 3), (7, 3), (3, 4)):
            tab = s4.table_of(s4.g_map(q, n), q, n + 1)
            per_t, size = s4.slice_data(tab, q, s4.last_coord(n))
            for t, (D, within) in enumerate(per_t):
                self.assertEqual(D, s4.D_closed(q, n, t), (q, n, t))
                for z in range(q):
                    self.assertEqual(size[z], q ** n)
                    want = s4.sum_N_squared(q, n) if (z + t) % q == 0 else q ** n
                    self.assertEqual(within[z], want, (q, n, t, z))


class TestTheorem46(unittest.TestCase):
    """C_q(n+1) holds for G_n: Lambda <= sliced bound < (n+1)(q-1)."""

    def test_brute(self):
        for q, n in ((3, 3), (5, 3), (7, 3), (3, 4), (11, 3)):
            k = n + 1
            tab = s4.table_of(s4.g_map(q, n), q, k)
            lam = s4.lam(tab, q, k)
            sb = s4.sliced_bound(tab, q, k, s4.last_coord(n))
            self.assertAlmostEqual(sb, s4.sliced_closed(q, n), places=9)
            self.assertLessEqual(lam, sb + 1e-9)
            self.assertLess(sb, k * (q - 1))
        # at q = 11 the Jensen bound of a166 exceeds 4(q-1) although Lambda is far below it
        tab = s4.table_of(s4.g_map(11, 3), 11, 4)
        self.assertGreater(s4.jensen_bound(s4.pibar(tab, 11, 4), 11), 40.5)
        self.assertLess(s4.lam(tab, 11, 4), 20)

    def test_closed_form_inequalities(self):
        for q in PRIMES[:25]:
            for n in range(3, 11):
                M = q ** (n + 1)
                self.assertLessEqual(s4.D_closed(q, n, 1), 2 * (q - 1) * q ** n)
                self.assertLess(s4.D_closed(q, n, 0) / M, 3.61)
                sb = s4.sliced_closed(q, n)
                self.assertLessEqual(sb, q - 0.1 + math.log2(q ** (n - 1) + 1))
                self.assertLess(sb, (n + 1) * (q - 1))

    def test_spin_sliced(self):
        # Theorem 45 applied to the spin-factor map (an instance of the general theorem)
        for q in (3, 5, 7):
            tab = s4.table_of(s4.spin_map(q, 3), q, 4)
            self.assertLessEqual(s4.lam(tab, q, 4),
                                 s4.sliced_bound(tab, q, 4, s4.last_coord(3)) + 1e-9)


if __name__ == "__main__":
    unittest.main()
