"""Tests for note a175 (twocodes.py). MV2 of Munim, Inc. Apache-2.0.
Made with AI agents working in MV2's name. Standard library only, self-contained.
Every assertion checks a fact proved in a175 (or an exact identity its proofs use).
Every entropy is computed by brute force over every point of F_q^k (q prime)."""
import math
import random
import unittest
from fractions import Fraction

import twocodes as tc


def _rand_mat(rng, q, k, r, density=1.0):
    return [[(rng.randrange(1, q) if rng.random() < density else 0) for _ in range(r)]
            for _ in range(k)]


def _with_diagonal(rng, q, M):
    D = [row[:] for row in M]
    for i in range(len(M)):
        D[i][i] = (D[i][i] + rng.randrange(q)) % q
    return D


# (q, k, r) triples with r <= k
CASES = [(3, 2, 1), (3, 3, 1), (3, 3, 2), (3, 4, 1), (3, 4, 2), (3, 4, 3), (3, 5, 2),
         (3, 5, 3), (3, 6, 2), (5, 2, 1), (5, 3, 1), (5, 3, 2), (5, 4, 2), (7, 2, 1),
         (7, 3, 1), (7, 3, 2)]


class TestRankIdentity(unittest.TestCase):
    """Proposition 68: H(Y|F) = H(Y|Q) + H(tau|F) - H(tau|Q) for F = Q(Y) + U V^T Y, any Q."""

    def test_any_map_Q(self):
        rng = random.Random(68)
        for q, k, r in CASES[:12]:
            pts = tc.all_points(q, k)
            for _ in range(3):
                table = {y: tuple(rng.randrange(q) for _ in range(k)) for y in pts}
                U = _rand_mat(rng, q, k, r, density=rng.choice([0.4, 0.8, 1.0]))
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.4, 0.8, 1.0]))
                Ut = tc.lin_map(q, V)

                def Q(y, table=table):
                    return table[y]

                def F(y, Q=Q, U=U, Ut=Ut):
                    t = Ut(y)
                    s = Q(y)
                    return tuple((s[i] + sum(U[i][l] * t[l] for l in range(r))) % q
                                 for i in range(k))
                lhs = tc.cond_entropy(pts, tc.ident, F)
                rhs = (tc.cond_entropy(pts, tc.ident, Q) + tc.cond_entropy(pts, Ut, F)
                       - tc.cond_entropy(pts, Ut, Q))
                self.assertAlmostEqual(lhs, rhs, places=9)

    def test_frames(self):
        rng = random.Random(681)
        for q, k, r in CASES:
            pts = tc.all_points(q, k)
            S = tc.square_map(q)
            self.assertAlmostEqual(tc.cond_entropy(pts, tc.ident, S), k * (q - 1) / q,
                                   places=9)
            for _ in range(2):
                U = _rand_mat(rng, q, k, r, density=0.8)
                V = _rand_mat(rng, q, k, r, density=0.8)
                M = tc.uvT(q, U, V)
                F = tc.frame_map(q, M)
                T = tc.lin_map(q, V)
                H = tc.cond_entropy(pts, tc.ident, F)
                rhs = (k * (q - 1) / q + tc.cond_entropy(pts, T, F)
                       - tc.cond_entropy(pts, T, S))
                self.assertAlmostEqual(H, rhs, places=9)


class TestLemma133Compatibility(unittest.TestCase):
    """E K <= sum_c prod (q + chi(-(Uc)_i))/(2q) <= W_U(theta); H(tau|F) <= log2 E K."""

    def test_counts(self):
        rng = random.Random(133)
        for q, k, r in CASES:
            for _ in range(2):
                U = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 1.0]))
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 1.0]))
                EK = tc.mean_compatible(q, U, V)
                cs = tc.compat_sum(q, U)
                self.assertLessEqual(EK, cs)
                self.assertLessEqual(cs, tc.W(q, U, tc.theta(q)))
                pts = tc.all_points(q, k)
                F = tc.frame_map(q, tc.uvT(q, U, V))
                HtF = tc.cond_entropy(pts, tc.lin_map(q, V), F)
                self.assertLessEqual(HtF, math.log2(EK) + 1e-12)

    def test_square_shift_probability(self):
        for q in (3, 5, 7, 11, 13):
            for a in range(1, q):
                n = sum(1 for y in range(q)
                        if any((z * z - y * y - a) % q == 0 for z in range(q)))
                self.assertEqual(n * 2, q + tc.chi(q, -a))
                self.assertLessEqual(Fraction(n, q), tc.theta(q))


class TestLemma134SignFourier(unittest.TestCase):
    """E_S |E[omega^(aY)|S]|^2 = 1/2 for a != 0; E_S sum_x P(tau=x|S)^2 = W_V(1/2) / q^r."""

    def test_half(self):
        for q in (3, 5, 7, 11, 13, 17):
            for a in range(1, q):
                self.assertAlmostEqual(tc.sign_fourier(q, a), 0.5, places=12)
            self.assertAlmostEqual(tc.sign_fourier(q, 0), 1.0, places=12)

    def test_collision_identity_exact(self):
        rng = random.Random(134)
        for q, k, r in CASES:
            for _ in range(2):
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.3, 0.7, 1.0]))
                self.assertEqual(tc.collision_given_square(q, V),
                                 tc.W(q, V, Fraction(1, 2)) / q ** r)

    def test_entropy_lower_bound(self):
        rng = random.Random(1341)
        for q, k, r in CASES:
            pts = tc.all_points(q, k)
            S = tc.square_map(q)
            for _ in range(2):
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 1.0]))
                h = tc.cond_entropy(pts, tc.lin_map(q, V), S)
                lb = r * math.log2(q) - math.log2(tc.W(q, V, Fraction(1, 2)))
                self.assertGreaterEqual(h, lb - 1e-12)


class TestTheorem60(unittest.TestCase):
    """H(M) <= k(1-1/q) - r log2 q + log2 W_U(theta) + log2 W_V(1/2), M = U V^T mod diagonal."""

    def test_bound(self):
        rng = random.Random(60)
        for q, k, r in CASES:
            for _ in range(3):
                U = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 0.8, 1.0]))
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 0.8, 1.0]))
                M = _with_diagonal(rng, q, tc.uvT(q, U, V))
                H = tc.frame_entropy(q, M)
                self.assertLessEqual(H, tc.theorem60_bound(q, U, V) + 1e-12)

    def test_column_worst_case(self):
        """Corollary 60.1: W_U(theta) <= a_q^r whenever U has full column rank."""
        rng = random.Random(601)
        for q, k, r in [(3, 3, 2), (3, 5, 2), (3, 5, 3), (3, 6, 4), (5, 4, 2), (5, 5, 3),
                        (7, 4, 2), (3, 8, 5)]:
            done = 0
            while done < 4:
                U = _rand_mat(rng, q, k, r, density=rng.choice([0.3, 0.6, 1.0]))
                if tc.rank_mod(U, q) != r:
                    continue
                done += 1
                self.assertLessEqual(tc.W(q, U, tc.theta(q)), tc.column_worst(q, r))
        # the coordinate code attains it
        for q, r in [(3, 3), (5, 2)]:
            I = [[1 if l == i else 0 for l in range(r)] for i in range(r)]
            self.assertEqual(tc.W(q, I, tc.theta(q)), tc.column_worst(q, r))

    def test_min_distance_corollary_arithmetic(self):
        """Corollary 60.2: r >= 2 and d >= r log2 a_q + 2 imply a_q^r (1 + (q^r-1) 2^-d) <= q^r."""
        for q in (3, 5, 7, 11, 13):
            a = 1 + (q - 1) * tc.theta(q)
            self.assertGreaterEqual((q / a) ** 2, Fraction(4, 3))
            for r in range(2, 41):
                d = math.ceil(r * math.log2(float(a)) + 2)
                self.assertLessEqual(a ** r * (1 + (q ** r - 1) * Fraction(1, 2 ** d)), q ** r)

    def test_min_distance_bounds_enumerator(self):
        rng = random.Random(602)
        for q, k, r in [(3, 6, 2), (3, 7, 3), (5, 5, 2)]:
            for _ in range(4):
                V = _rand_mat(rng, q, k, r)
                if tc.rank_mod(V, q) != r:
                    continue
                hist = tc.weight_hist(q, V)
                d = min(w for w in hist if w > 0)
                self.assertEqual(hist[0], 1)
                self.assertLessEqual(tc.enumerator(hist, Fraction(1, 2)),
                                     1 + (q ** r - 1) * Fraction(1, 2 ** d))


class TestTheorem61(unittest.TestCase):
    """H(M) >= k(1-1/q) - H(tau|S) >= k(1-1/q) - r log2 q; all-c family deficit -> log2 q."""

    def test_lower_bound(self):
        rng = random.Random(61)
        for q, k, r in CASES:
            pts = tc.all_points(q, k)
            for _ in range(3):
                U = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 1.0]))
                V = _rand_mat(rng, q, k, r, density=rng.choice([0.5, 1.0]))
                M = _with_diagonal(rng, q, tc.uvT(q, U, V))
                H = tc.frame_entropy(q, M)
                hts = tc.cond_entropy(pts, tc.lin_map(q, V), tc.square_map(q))
                self.assertGreaterEqual(H, k * (q - 1) / q - hts - 1e-9)
                self.assertGreaterEqual(H, k * (q - 1) / q - r * math.log2(q) - 1e-12)

    def test_all_c_family(self):
        for q, k in [(3, 2), (3, 3), (3, 4), (3, 5), (3, 6), (3, 7), (5, 2), (5, 3), (5, 4),
                     (7, 2), (7, 3)]:
            th = (q + 1) / (2 * q)
            for c in range(1, q):
                M = [[c] * k for _ in range(k)]
                H = tc.frame_entropy(q, M)
                deficit = k * (q - 1) / q - H
                self.assertLessEqual(deficit, math.log2(q) + 1e-12)
                lower = (math.log2(q) - math.log2(1 + (q - 1) * th ** k)
                         - math.log2(1 + (q - 1) * 2.0 ** (-k)))
                self.assertGreaterEqual(deficit, lower - 1e-12)
                # Lambda of x o x + cJx: every slice M + tI has the same entropy
                lam = sum(tc.frame_entropy(q, [[(M[i][j] + (t if i == j else 0)) % q
                                                for j in range(k)] for i in range(k)])
                          for t in range(q))
                self.assertAlmostEqual(lam, q * H, places=9)
                self.assertLessEqual(lam, k * (q - 1) - q * lower + 1e-9)
                self.assertGreaterEqual(lam, k * (q - 1) - q * math.log2(q) - 1e-9)


class TestCertificate(unittest.TestCase):
    """Proposition 69: a strongly connected rank-11 frame on F_3^28 that Theorem 60 certifies,
    while Corollary 58.1 (k > 14) and Theorem 59 (for every J) do not."""

    def test_instance(self):
        q, r, k = 3, 11, 28
        found = tc.certificate_instance(q, r, k)
        self.assertIsNotNone(found)
        seed, U, V, M, WU, WV = found
        self.assertEqual(len(M), k)
        self.assertEqual(tc.rank_mod(M, q), r)
        self.assertEqual(tc.rank_mod(V, q), r)
        self.assertTrue(tc.strongly_connected(M))
        th = tc.theta(q)
        # closed form of W_U(theta) for this U: c_0 sits on 18 coordinates
        self.assertEqual(WU, (1 + 2 * th ** 18) * (1 + 2 * th) ** 10)
        self.assertEqual(sum(tc.weight_hist(q, V).values()), q ** r)
        self.assertLessEqual(2 * WU * WV, q ** r)
        bound = k * (q - 1) / q - r * math.log2(q) + math.log2(WU) + math.log2(WV)
        self.assertLess(bound, k * (q - 1) / q - 0.999)
        # Theorem 59 with this factorization: B_J >= (2 - 1/q)^(r-1) - 1 for every J, so its
        # bound is at least (k-r)(1-1/q) + (r-1) log2(2-1/q) > k(1-1/q)
        self.assertGreater((k - r) * (q - 1) / q + (r - 1) * math.log2(2 - 1 / q),
                           k * (q - 1) / q + 0.02)
        # and k exceeds K0(3) = 14 (a174, Corollary 58.1)
        self.assertGreater(k, 14)


if __name__ == "__main__":
    unittest.main()
