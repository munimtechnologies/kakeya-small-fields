"""Tests for note a171 (split partner covers force frame products). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion checks a fact proved in a171.md. All q are odd primes. Group computations are
brute force over ALL k x k matrices, so they do not rely on the proofs they test.
"""
import itertools
import math
import random
import unittest

import splitgroup as sg

EPS = 1e-9


def is_involution_matrix(M, q):
    k = len(M)
    return sg.mat_mul(M, M, q) == sg.identity(k)


def check_partner_group(tc, table, q, k, mats, gl):
    """Proposition 60 on one nondegenerate quadratic map."""
    G = sg.affine_partners(table, q, k, mats)
    I = sg.identity(k)
    zero = (0,) * k
    ident = (I, zero, zero)
    elems = set(G)
    tc.assertEqual(len(elems), len(G))
    tc.assertLessEqual(len(G), 2 ** k - 1)
    tc.assertIn(len(G) + 1, [2 ** m for m in range(k + 1)])
    for g in G:
        tc.assertEqual(sg.compose(g, g, q), ident)          # every element is an involution
        tc.assertIsNotNone(sg.mat_inv(g[0], q))
        for h in G:
            gh = sg.compose(g, h, q)
            tc.assertTrue(gh == ident or gh in elems)        # closed under composition
            tc.assertEqual(gh, sg.compose(h, g, q))          # abelian
    frame = sg.is_frame_conjugate(table, q, k, gl)
    tc.assertEqual(len(G) == 2 ** k - 1, frame)              # equality iff frame product
    return len(G), frame


class TestJensenPairBound(unittest.TestCase):
    """Theorem 51, step 1 (any map): Lambda <= sum_t log2(N_t/q^k) <= q log2(1 + M/q^(k+1))."""

    def test_random_functions(self):
        rng = random.Random(1711)
        for q, k in [(3, 1), (5, 1), (7, 1), (3, 2), (5, 2), (3, 3)]:
            n = q ** k
            for _ in range(6):
                table = [tuple(rng.randrange(q) for _ in range(k)) for _ in range(n)]
                lam, M, jt = sg.lam_pairs(table, q, k)
                self.assertLessEqual(lam, jt + EPS)
                self.assertLessEqual(jt, q * math.log2(1 + M / (q * n)) + EPS)

    def test_random_quadratic(self):
        rng = random.Random(1712)
        for q, k in [(3, 2), (5, 2), (7, 2), (3, 3), (5, 3)]:
            n = q ** k
            for _ in range(5):
                table = sg.table_of(sg.random_quadratic(q, k, rng), q, k)
                lam, M, jt = sg.lam_pairs(table, q, k)
                self.assertLessEqual(lam, jt + EPS)
                self.assertLessEqual(jt, q * math.log2(1 + M / (q * n)) + EPS)


class TestFrames(unittest.TestCase):
    """Frame products and their conjugates: Lambda = k(q-1), M = q(2q-1)^k - q^(k+1)."""

    def test_frames(self):
        rng = random.Random(1713)
        for q, k in [(3, 1), (5, 1), (7, 1), (3, 2), (5, 2), (7, 2), (3, 3), (5, 3)]:
            for _ in range(3):
                table = sg.table_of(sg.frame_quadratic(q, k, rng), q, k)
                E, Ei = sg.random_gl(q, k, rng)
                for tab in (table, sg.conjugate_table(table, E, Ei, q, k)):
                    lam, M, jt = sg.lam_pairs(tab, q, k)
                    self.assertAlmostEqual(lam, k * (q - 1), delta=1e-9)
                    self.assertEqual(M, q * (2 * q - 1) ** k - q ** (k + 1))


class TestOrthogonalGroup(unittest.TestCase):
    """Lemma 126: for nondegenerate Q (q odd) every M with Q(Mx) = Q(x) is an involution, and
    O(Q) is an elementary abelian 2-group of order at most 2^k."""

    def check(self, table, q, k, mats):
        O = sg.orthogonal_group(table, q, k, mats)
        self.assertIn(len(O), [2 ** m for m in range(1, k + 1)])   # contains +-I
        for M in O:
            self.assertTrue(is_involution_matrix(M, q))
            for N in O:
                self.assertEqual(sg.mat_mul(M, N, q), sg.mat_mul(N, M, q))
        return O

    def test_binary_exhaustive_q3(self):
        q, k = 3, 2
        mats = sg.all_matrices(q, k)
        count = 0
        for coeffs in itertools.product(range(q), repeat=6):
            Qc = [[[coeffs[0], coeffs[1]], [0, coeffs[2]]],
                  [[coeffs[3], coeffs[4]], [0, coeffs[5]]]]
            if sg.binary_resultant(Qc, q) == 0:
                continue
            count += 1
            P = (Qc, [[0, 0], [0, 0]], [0, 0])
            self.check(sg.table_of(P, q, k), q, k, mats)
        self.assertGreater(count, 100)

    def test_binary_random(self):
        rng = random.Random(1714)
        for q in (5, 7):
            mats = sg.all_matrices(q, 2)
            done = 0
            while done < 12:
                P = sg.random_quadratic(q, 2, rng)
                if sg.binary_resultant(P[0], q) == 0:
                    continue
                done += 1
                self.check(sg.table_of(P, q, 2), q, 2, mats)

    def test_frame_and_field_square(self):
        rng = random.Random(1715)
        for q, k in [(3, 2), (5, 2), (3, 3)]:
            mats = sg.all_matrices(q, k)
            for _ in range(2):
                table = sg.table_of(sg.frame_quadratic(q, k, rng), q, k)
                E, Ei = sg.random_gl(q, k, rng)
                O = self.check(sg.conjugate_table(table, E, Ei, q, k), q, k, mats)
                self.assertEqual(len(O), 2 ** k)
            O = self.check(sg.field_square_table(q, k), q, k, mats)
            self.assertEqual(len(O), 2)


class TestPartnerGroup(unittest.TestCase):
    """Proposition 60: G(P) is an elementary abelian 2-group of order <= 2^k, with equality
    exactly for maps that are F_q-conjugate to a frame product."""

    def test_plane_q3_all_top_forms(self):
        q, k = 3, 2
        rng = random.Random(1716)
        mats = sg.all_matrices(q, k)
        gl = sg.general_linear(q, k)
        frames = 0
        sizes = set()
        for coeffs in itertools.product(range(q), repeat=6):
            Qc = [[[coeffs[0], coeffs[1]], [0, coeffs[2]]],
                  [[coeffs[3], coeffs[4]], [0, coeffs[5]]]]
            if sg.binary_resultant(Qc, q) == 0:
                continue
            for L in ([[0, 0], [0, 0]], [[rng.randrange(q) for _ in range(2)] for _ in range(2)]):
                P = (Qc, L, [rng.randrange(q), rng.randrange(q)])
                size, frame = check_partner_group(self, sg.table_of(P, q, k), q, k, mats, gl)
                sizes.add(size)
                frames += frame
        self.assertGreater(frames, 0)
        self.assertTrue(sizes <= {0, 1, 3})
        self.assertIn(3, sizes)

    def test_plane_q5_q7(self):
        rng = random.Random(1717)
        for q, nrand, nframe in [(5, 14, 4), (7, 3, 2)]:
            mats = sg.all_matrices(q, 2)
            gl = sg.general_linear(q, 2)
            done = 0
            while done < nrand:
                P = sg.random_quadratic(q, 2, rng)
                if sg.binary_resultant(P[0], q) == 0:
                    continue
                done += 1
                check_partner_group(self, sg.table_of(P, q, 2), q, 2, mats, gl)
            for _ in range(nframe):
                table = sg.table_of(sg.frame_quadratic(q, 2, rng), q, 2)
                E, Ei = sg.random_gl(q, 2, rng)
                size, frame = check_partner_group(
                    self, sg.conjugate_table(table, E, Ei, q, 2), q, 2, mats, gl)
                self.assertEqual(size, 3)
                self.assertTrue(frame)

    def test_field_square_plane(self):
        for q in (3, 5, 7):
            mats = sg.all_matrices(q, 2)
            gl = sg.general_linear(q, 2)
            size, frame = check_partner_group(self, sg.field_square_table(q, 2), q, 2, mats, gl)
            self.assertEqual(size, 1)
            self.assertFalse(frame)

    def test_space_q3(self):
        q, k = 3, 3
        rng = random.Random(1718)
        mats = sg.all_matrices(q, k)
        gl = sg.general_linear(q, k)
        for _ in range(2):
            table = sg.table_of(sg.frame_quadratic(q, k, rng), q, k)
            E, Ei = sg.random_gl(q, k, rng)
            size, frame = check_partner_group(
                self, sg.conjugate_table(table, E, Ei, q, k), q, k, mats, gl)
            self.assertEqual(size, 7)
            self.assertTrue(frame)
        size, frame = check_partner_group(self, sg.field_square_table(q, k), q, k, mats, gl)
        self.assertEqual(size, 1)
        self.assertFalse(frame)
        L = tuple(tuple(rng.randrange(q) for _ in range(k)) for _ in range(k))
        size, frame = check_partner_group(self, sg.field_square_table(q, k, L), q, k, mats, gl)
        self.assertLessEqual(size, 1)
        self.assertFalse(frame)


class TestThreshold(unittest.TestCase):
    """Remark 51.1 / Corollary 52.1: arithmetic of the threshold q0(k)."""

    def test_q0(self):
        ranges = {2: (600, 700), 3: (25000, 32000), 4: (700000, 900000),
                  5: (16000000, 21000000)}
        for k, (lo, hi) in ranges.items():
            q0 = sg.q0_case_a(k)
            self.assertTrue(lo <= q0 <= hi, (k, q0))
            self.assertTrue(sg.case_a_ok(k, q0))
            self.assertFalse(sg.case_a_ok(k, q0 - 1))
            for j in range(40):
                self.assertTrue(sg.case_a_ok(k, q0 + j * (q0 // 9 + 1)))
            self.assertTrue(sg.case_a_ok(k, 10 ** 12))


if __name__ == "__main__":
    unittest.main()
