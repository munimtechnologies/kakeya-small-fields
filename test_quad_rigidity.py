# SPDX-License-Identifier: Apache-2.0
"""Tests for quad_rigidity.py (note a163, Theorem 38). Standard library only.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Every assertion is a fact proved by hand in a163, so a failure means either a bug in
the code or an error in the hand proof; the commit carrying a163 ships only if all pass.
"""

import itertools
import random
import unittest

import quad_rigidity as qr


def check_map(tc, F, P):
    """Theorem 38 and Lemma 114 for one degree <= 2 map P. Returns (is_max, has_full)."""
    q = F.q
    pis = {w: qr.pi_w(F, P, w) for w in qr.directions(q)}
    full = [w for w, v in pis.items() if v == q * q * (q - 1)]
    score = qr.score_int(F, P)
    bound = qr.bound_int(F)
    # Lemma 112 + log2 z <= z - 1: q^2 Lambda <= sum_w Pi_w
    tc.assertLessEqual(score, 2 ** sum(pis.values()))
    # Theorem 38: never above 2 (q - 1)
    tc.assertLessEqual(score, bound)
    if not full:
        # Lemma 114 and Case A of Theorem 38: strictly below
        for w, v in pis.items():
            tc.assertLessEqual(v, qr.nonfull_cap(F), (q, w))
        tc.assertLess(score, bound)
    m = score == bound
    if m:
        tc.assertIsNotNone(qr.frame_of(F, P))
    return m, bool(full)


class TestFields(unittest.TestCase):
    def test_tables(self):
        for q in (2, 3, 4, 5, 7, 8):
            F = qr.Field(q)
            nonzero = range(1, q)
            for a in range(q):
                self.assertEqual(F.A[a][F.N[a]], 0)
                self.assertEqual(sorted(F.A[a][b] for b in range(q)), list(range(q)))
            for a in nonzero:
                self.assertEqual(F.M[a][F.I[a]], 1)
                self.assertEqual(sorted(F.M[a][b] for b in nonzero), list(nonzero))
            for a, b, c in itertools.product(range(q), repeat=3):
                self.assertEqual(F.M[a][F.A[b][c]], F.A[F.M[a][b]][F.M[a][c]])
                self.assertEqual(F.M[F.M[a][b]][c], F.M[a][F.M[b][c]])


class TestExhaustiveQ3(unittest.TestCase):
    """Every degree <= 2 map of F_3^2 without constant term (3^10 = 59,049 maps)."""

    def test_all(self):
        F = qr.Field(3)
        nmax = 0
        for c in itertools.product(range(3), repeat=10):
            P = qr.quad_map(F, c[:5], c[5:])
            m, full = check_map(self, F, P)
            nmax += m
            if not m and full and qr.frame_of(F, P) is not None:
                self.fail("frame product that is not maximal")
        # Prop 43 (a162): the maximisers with P(0) = 0 are the 216 frame products, and
        # every frame product of quadratics has degree 2; Theorem 38 says they are all
        self.assertEqual(nmax, 216)
        print("q = 3: 59,049 degree-2 maps, maximisers", nmax)


class TestTriangularExhaustive(unittest.TestCase):
    """Propositions 45 / 46: the exact maximisers among triangular degree-2 maps."""

    def run_q(self, q):
        F = qr.Field(q)
        n = 0
        for al, be, ga, de, ze, et in itertools.product(range(q), repeat=6):
            P = qr.triangular(F, al, be, ga, de, ze, et)
            self.assertIn((1, 0), qr.full_directions(F, P))
            score = qr.score_int(F, P)
            self.assertLessEqual(score, qr.bound_int(F))  # Theorem 4
            m = score == qr.bound_int(F)
            self.assertEqual(m, qr.predicted_max(F, al, be, ga, de, ze, et),
                             (q, al, be, ga, de, ze, et))
            if m:
                n += 1
                self.assertIsNotNone(qr.frame_of(F, P))
        self.assertEqual(n, qr.predicted_count(q))
        print("q =", q, "triangular family", q ** 6, "maps, maximisers", n)

    def test_q3(self):
        self.run_q(3)

    def test_q4(self):
        self.run_q(4)

    def test_q5(self):
        self.run_q(5)


class TestRandom(unittest.TestCase):
    """Random degree-2 maps, random triangular maps in random bases, and random
    one-coefficient perturbations of frame products, for q = 4, 5, 7, 8."""

    def test_random(self):
        rng = random.Random(163)
        for q, reps in ((4, 120), (5, 120), (7, 60), (8, 40)):
            F = qr.Field(q)
            nfull = 0
            for r in range(reps):
                kind = r % 3
                if kind == 0:  # general degree-2 map
                    c = [rng.randrange(q) for _ in range(10)]
                    P = qr.quad_map(F, c[:5], c[5:])
                else:
                    al, be = rng.randrange(1, q), rng.randrange(1, q)
                    kappa, et = rng.randrange(q), rng.randrange(q)
                    if F.p != 2:
                        ga = F.M[F.N[F.M[F.two()][al]]][kappa]
                    else:
                        ga = 0
                    de = F.A[F.M[al][F.M[kappa][kappa]]][F.M[kappa][be]]
                    ze = F.M[kappa][et]
                    coeffs = [al, be, ga, de, ze, et]
                    if kind == 2:  # perturb one coefficient
                        i = rng.randrange(6)
                        coeffs[i] = F.A[coeffs[i]][rng.randrange(1, q)]
                    P = qr.triangular(F, *coeffs)
                    self.assertEqual(qr.is_max(F, P), qr.predicted_max(F, *coeffs))
                    if kind == 1:
                        self.assertTrue(qr.is_max(F, P))
                    while True:
                        g = ((rng.randrange(q), rng.randrange(q)),
                             (rng.randrange(q), rng.randrange(q)))
                        if F.sub(F.M[g[0][0]][g[1][1]], F.M[g[0][1]][g[1][0]]) != 0:
                            break
                    P2 = qr.conjugate(F, P, g)
                    self.assertEqual(qr.score_int(F, P2), qr.score_int(F, P))
                    P = P2
                m, full = check_map(self, F, P)
                nfull += full
                if kind == 1:
                    self.assertTrue(m)
            print("q =", q, "random maps", reps, "with a full direction", nfull)


if __name__ == "__main__":
    unittest.main(verbosity=2)
