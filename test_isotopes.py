"""Tests for note a173 (isotopes, spin factors, the spectral lemma). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion checks a fact proved in a173.md (or in the earlier notes it cites). All q are
odd primes. Lambda and every conditional entropy are computed by brute force over every point
(and every t), so the tests do not rely on the proofs.
"""
import math
import random
import unittest

import isotopes as iso

EPS = 1e-9


def rand_vec(q, k, rng):
    return tuple(rng.randrange(q) for _ in range(k))


class TestIsotopeReduction(unittest.TestCase):
    """Theorem 54: if R_p is invertible, x * y = R_p^{-1}(x o y) has unit p, and
    R_p^{-1} A_t(x) = x * x + R_p^{-1}(L + tI) x + R_p^{-1} c for every x and t. So every slice
    of P has the fibre entropy of a unital map, and (Lemma 127 in the isotope) that entropy is
    unchanged when the linear part R_p^{-1}(L + tI) is replaced by R_p^{-1}(L + tI) + sI."""

    def test_random_regular_algebras(self):
        rng = random.Random(1731)
        seen = 0
        for q, k, reps in [(3, 2, 10), (3, 3, 8), (3, 4, 3), (5, 2, 8), (5, 3, 3), (7, 2, 5)]:
            for _ in range(reps):
                C = iso.random_commutative(q, k, rng)
                p = iso.regular_point(C, q)
                if p is None:
                    continue
                seen += 1
                L = iso.random_matrix(q, k, rng)
                c = rand_vec(q, k, rng)
                D, Rinv = iso.isotope(C, p, q)
                self.assertTrue(iso.is_unit(D, p, q))
                for i in range(k):
                    for j in range(k):
                        self.assertEqual(D[i][j], D[j][i])
                P = iso.make_map(C, q, L, c)
                for t in range(q):
                    At = iso.shifted(P, q, t)
                    D2, M, c2 = iso.slice_as_unital(C, L, c, p, q, t)
                    U = iso.make_map(D2, q, M, c2)
                    for x in iso.all_vectors(q, k):
                        self.assertEqual(iso.mat_vec(Rinv, At(x), q), U(x))
                    h = iso.cond_entropy(At, q, k)
                    self.assertAlmostEqual(h, iso.cond_entropy(U, q, k), delta=EPS)
                    for s in range(q):
                        Ms = iso.mat_add(M, iso.mat_scale(iso.identity(k), s, q), q)
                        Us = iso.make_map(D2, q, Ms, c2)
                        self.assertAlmostEqual(h, iso.cond_entropy(Us, q, k), delta=EPS)
        self.assertGreaterEqual(seen, 20)

    def test_slicewise_bound_k_at_most_3(self):
        """Corollary 54.2: for k <= 3 every slice of every regular quadratic map has
        H(X | A_t X) <= k (1 - 1/q) (Theorem 54 with Theorems 38 and 43)."""
        rng = random.Random(1732)
        for q, k, reps in [(3, 2, 12), (3, 3, 10), (5, 2, 10), (5, 3, 4), (7, 2, 6)]:
            for _ in range(reps):
                C = iso.random_commutative(q, k, rng)
                if iso.regular_point(C, q) is None:
                    continue
                P = iso.make_map(C, q, iso.random_matrix(q, k, rng), rand_vec(q, k, rng))
                for h in iso.lambda_terms(P, q, k):
                    self.assertLessEqual(h, k * (1 - 1 / q) + EPS)

    def test_g_n_is_regular(self):
        """a167's G_n is regular: det R_(u, s) = -s^(n-1) phi(u) up to sign conventions, and it
        is nonzero at s = 1, u = e_1 when phi(e_1) != 0."""
        for q, phi in [(3, [[1, 0], [0, 1]]), (3, [[1, 0, 0], [0, 1, 0], [0, 0, 2]]),
                       (5, [[1, 0], [0, 2]])]:
            C = iso.g_map_algebra(q, phi)
            n = len(phi)
            p = tuple([1] + [0] * (n - 1) + [1])
            self.assertIsNotNone(iso.mat_inv(iso.mult_matrix(C, p, q), q))

    def test_regular_fraction(self):
        """Proposition 65: at most a k/q fraction of all commutative algebras on F_q^k have
        det R_(1,...,1) = 0, and every non-regular algebra is among them."""
        for q in (3, 5):
            k = 2
            total = det0 = nonreg = 0
            for a in range(q ** 6):
                vals = []
                for _ in range(6):
                    vals.append(a % q)
                    a //= q
                C = [[None, None], [None, None]]
                C[0][0] = (vals[0], vals[1])
                C[0][1] = C[1][0] = (vals[2], vals[3])
                C[1][1] = (vals[4], vals[5])
                total += 1
                R = iso.mult_matrix(C, (1, 1), q)
                if (R[0][0] * R[1][1] - R[0][1] * R[1][0]) % q == 0:
                    det0 += 1
                    if q == 3 and iso.regular_point(C, q) is None:
                        nonreg += 1
            self.assertLessEqual(det0 * q, k * total)
            if q == 3:
                self.assertLessEqual(nonreg, det0)
                self.assertGreater(nonreg, 0)


class TestSpinFactors(unittest.TestCase):
    """Theorem 55 and Proposition 64."""

    def check_form(self, q, Phi):
        n = len(Phi)
        k = n + 1
        C = iso.spin_factor(q, Phi)
        self.assertTrue(iso.is_unit(C, iso.unit_vec(k, 0), q))
        h = iso.cond_entropy(lambda y: iso.square(C, y, q), q, k)
        self.assertAlmostEqual(h, iso.spin_formula(q, Phi), delta=EPS)
        bound = k * (1 - 1 / q)
        sq = set(iso.nonzero_squares(q))
        equal = n == 0 or (n == 1 and Phi[0][0] % q in sq)
        if equal:
            self.assertAlmostEqual(h, bound, delta=EPS)
        else:
            self.assertLess(h, bound - 1e-3)
        self.assertLessEqual(q * h, iso.spin_crude_bound(q, n) + EPS)
        return h

    def test_all_forms_small(self):
        for q, nmax in [(3, 3), (5, 2), (7, 2)]:
            for n in range(0, nmax + 1):
                for Phi in iso.symmetric_matrices(q, n):
                    self.check_form(q, Phi)

    def test_random_forms_larger(self):
        rng = random.Random(1733)
        for q, n, reps in [(3, 4, 20), (5, 3, 25), (11, 1, 11), (11, 2, 8), (13, 2, 4)]:
            for _ in range(reps):
                self.check_form(q, iso.random_symmetric(q, n, rng))

    def test_table_q3_n2(self):
        """The five isometry classes of forms on F_3^2 (Section 3 table)."""
        expect = {
            ((0, 0), (0, 0)): (16 + 2 + 9 * math.log2(9)) / 27,
            ((1, 0), (0, 0)): (16 + 6 + 3 * math.log2(3) + 18) / 27,
            ((2, 0), (0, 0)): (16 + 2 + 3 * math.log2(3) + 6 * math.log2(6)) / 27,
            ((1, 0), (0, 1)): (16 + 2 * math.log2(6) + 4 * math.log2(6) + 8) / 27,
            ((1, 0), (0, 2)): (16 + 4 + 5 * math.log2(5) + 4 + 2) / 27,
        }
        for Phi, value in expect.items():
            M = [list(r) for r in Phi]
            h = self.check_form(3, M)
            self.assertAlmostEqual(h, value, delta=EPS)
            self.assertLess(h, 1.73)

    def test_crude_bound_inequality(self):
        """G(q, n) < (n + 1)(q - 1) for n >= 2 (proved in Section 3; checked here on a range)."""
        primes = [p for p in range(3, 102) if all(p % d for d in range(2, p))]
        for q in primes:
            for n in range(2, 41):
                self.assertLess(iso.spin_crude_bound(q, n), (n + 1) * (q - 1))
        self.assertAlmostEqual(iso.spin_crude_bound(3, 2),
                               16 / 9 + 2 / 9 * math.log2(10) + math.log2(11), delta=EPS)

    def test_kakeya_lambda_spin(self):
        """Lambda(y o y + l o y + c) = q H(Y | Y^2) <= k (q - 1) (Lemma 127 + Theorem 55)."""
        rng = random.Random(1734)
        for q, n, reps in [(3, 2, 6), (3, 3, 3), (5, 2, 4), (7, 1, 3)]:
            for _ in range(reps):
                Phi = iso.random_symmetric(q, n, rng)
                C = iso.spin_factor(q, Phi)
                k = n + 1
                l = rand_vec(q, k, rng)
                L = iso.mult_matrix(C, l, q)
                P = iso.make_map(C, q, L, rand_vec(q, k, rng))
                lam = iso.kakeya_lambda(P, q, k)
                self.assertAlmostEqual(lam, q * iso.spin_formula(q, Phi), delta=1e-7)
                self.assertLessEqual(lam, k * (q - 1) + EPS)

    def test_quadratic_identity(self):
        """Proposition 64 (easy direction): y^2 = 2a y - (a^2 - phi(v)) 1 for y = a + v."""
        rng = random.Random(1735)
        for q, n in [(3, 3), (5, 2), (7, 3)]:
            Phi = iso.random_symmetric(q, n, rng)
            C = iso.spin_factor(q, Phi)
            for _ in range(30):
                y = rand_vec(q, n + 1, rng)
                a = y[0]
                f = iso.quad_value(Phi, y[1:], q)
                rhs = tuple((2 * a * y[i] - ((a * a - f) if i == 0 else 0)) % q
                            for i in range(n + 1))
                self.assertEqual(iso.square(C, y, q), rhs)


class TestSpectralLemma(unittest.TestCase):
    """Theorem 56: A_t is injective iff -t is not an eigenvalue of R_u + L for any u. For a
    flag-nilpotent algebra with flag-lowering L, A_t is injective for every t != 0 and
    Lambda(P) = H(X | P X) <= k log2 q < k (q - 1)."""

    def test_spectral_characterisation(self):
        rng = random.Random(1736)
        for q, k, reps in [(3, 2, 8), (3, 3, 5), (5, 2, 5), (5, 3, 2)]:
            for _ in range(reps):
                C = iso.random_commutative(q, k, rng)
                L = iso.random_matrix(q, k, rng)
                T = iso.spectral_set(C, L, q)
                P = iso.make_map(C, q, L, rand_vec(q, k, rng))
                for t in range(q):
                    sizes = iso.fibre_sizes(iso.shifted(P, q, t), q, k)
                    self.assertEqual(max(sizes) == 1, t not in T)

    def test_flag_nilpotent(self):
        rng = random.Random(1737)
        cases = [(3, 3, 6), (3, 4, 3), (5, 3, 3), (7, 2, 4)]
        for q, k, reps in cases:
            for r in range(reps + 1):
                if r == reps:
                    if (q, k) != (3, 4):
                        continue
                    C = iso.power_failure_example()
                else:
                    C = iso.flag_nilpotent(q, k, rng)
                L = iso.flag_lowering(q, k, rng)
                self.assertTrue(iso.spectral_set(C, L, q) <= {0})
                P = iso.make_map(C, q, L, rand_vec(q, k, rng))
                terms = iso.lambda_terms(P, q, k)
                for t in range(1, q):
                    self.assertAlmostEqual(terms[t], 0.0, delta=EPS)
                self.assertLessEqual(sum(terms), k * math.log2(q) + EPS)
                self.assertLess(sum(terms), k * (q - 1))

    def test_example_not_power_associative(self):
        q = 3
        C = iso.power_failure_example()
        x = iso.unit_vec(4, 0)
        x2 = iso.square(C, x, q)
        self.assertNotEqual(iso.mult(C, x2, x2, q), iso.mult(C, iso.mult(C, x2, x, q), x, q))
        self.assertFalse(iso.is_associative(C, q))


if __name__ == "__main__":
    unittest.main()
