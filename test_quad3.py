# SPDX-License-Identifier: Apache-2.0
"""Tests for quad3.py (note a164: Theorem 39, Proposition 47, Theorem 40).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a164 (or in a163,
Theorem 38, or the 1D bound C_q(1)), so a failure means a bug in the code or an error in
the hand proof. The commit carrying a164 ships only if all pass.
"""

import random
import unittest

import quad3 as q3


def rand_quad(rng, q):
    Qc = [[rng.randrange(q) for _ in range(6)] for _ in range(3)]
    Lm = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
    return q3.quad_map3(q, Qc, Lm)


def rand_gl3(rng, q):
    while True:
        A = [[rng.randrange(q) for _ in range(3)] for _ in range(3)]
        if q3.rank(q, A) == 3:
            return A


def check_general(tc, q, P, planes):
    """Facts true for EVERY map P of F_q^3 (any degree)."""
    pis = q3.all_pi(q, P)
    score = q3.score_int(q, P)
    # Lemma 112 in dimension 3 (log2 z <= z - 1): q^3 Lambda <= sum_w Pi_w
    tc.assertLessEqual(score, 2 ** sum(pis.values()))
    # Theorem 39 (splitting inequality) for the chosen planes
    for n in planes:
        scores, out_pairs = q3.split_terms(q, P, n, pis)
        prod = 1
        for s in scores:
            prod *= s
        tc.assertLessEqual(score, prod * 2 ** out_pairs, (q, n))
    return pis, score


def check_quad(tc, q, P, planes):
    """Facts for a map of degree <= 2 and odd prime q. Returns the classify() dict."""
    pis, score = check_general(tc, q, P, planes)
    bound2 = q3.bound_int(q, 2)  # 2^(2 (q-1) q^2)
    # Theorem 38 (a163) on every projected coset map: each coset score <= 2^(2(q-1)q^2)
    for n in planes:
        scores, _ = q3.split_terms(q, P, n, pis)
        for s in scores:
            tc.assertLessEqual(s, bound2, (q, n))
    # Proposition 47: exact pair counts from ranks
    for w, v in pis.items():
        tc.assertEqual(v, q3.predicted_pi(q, P, w), (q, w))
    c = q3.classify(q, P, pis)
    bound = q3.bound_int(q)
    # an invariant line is exactly an active direction of rank 0
    for w in q3.directions(q):
        r, act, _ = c["rank_data"][w]
        tc.assertEqual(w in c["inv_lines"], r == 0 and act, (q, w))
    if c["inv"]:
        # Theorem 40 (a): Theorem 4 + Theorem 38 + C_q(1)
        tc.assertLessEqual(score, bound)
    else:
        # with no invariant line every Pi_w is 0, (q-1)q or (q-1)q^2
        for w, v in pis.items():
            tc.assertIn(v, (0, (q - 1) * q, (q - 1) * q * q), (q, w))
            tc.assertEqual(v == (q - 1) * q * q, w in c["D"])
        if c["cond_b"] or c["cond_c"]:
            # Theorem 40 (b), (c)
            tc.assertLessEqual(score, bound)
    return c


class TestBasics(unittest.TestCase):
    def test_counts(self):
        for q in (3, 5, 7):
            self.assertEqual(len(q3.directions(q)), q * q + q + 1)
            self.assertEqual(len(q3.points(q)), q ** 3)

    def test_rank(self):
        self.assertEqual(q3.rank(5, [(1, 2, 3), (2, 4, 6)]), 1)
        self.assertEqual(q3.rank(5, [(1, 0, 0), (0, 1, 0), (1, 1, 0)]), 2)
        self.assertEqual(q3.rank(7, [(1, 0, 0), (0, 1, 0), (0, 0, 3)]), 3)
        self.assertEqual(q3.rank(3, [(0, 0, 0)]), 0)

    def test_frame_products(self):
        """Frame products in dimension 3 attain 3(q-1) exactly (also after a change
        of basis), and respect coordinate subspaces."""
        rng = random.Random(1640)
        for q, reps in ((3, 4), (5, 4), (7, 2)):
            for _ in range(reps):
                a = [rng.randrange(1, q) for _ in range(3)]
                b = [rng.randrange(q) for _ in range(3)]
                P = q3.frame3(q, a, b)
                self.assertEqual(q3.score_int(q, P), q3.bound_int(q))
                P2 = q3.conjugate(q, P, rand_gl3(rng, q))
                self.assertEqual(q3.score_int(q, P2), q3.bound_int(q))
                pis = q3.all_pi(q, P2)
                self.assertGreaterEqual(len(q3.invariant_lines(q, pis)), 3)


class TestArbitraryMaps(unittest.TestCase):
    """Theorem 39 and the pair bound hold for every map, not only degree 2."""

    def test_arbitrary(self):
        rng = random.Random(1641)
        for q, reps in ((3, 40), (5, 6)):
            pts = q3.points(q)
            dirs = q3.directions(q)
            for r in range(reps):
                if r % 2 == 0:
                    P = [tuple(rng.randrange(q) for _ in range(3)) for _ in pts]
                else:  # few values: many collisions
                    vals = [tuple(rng.randrange(q) for _ in range(3)) for _ in range(3)]
                    P = [rng.choice(vals) for _ in pts]
                planes = dirs if q == 3 else rng.sample(dirs, 8)
                check_general(self, q, P, planes)


class TestDegreeTwo(unittest.TestCase):
    def run_family(self, q, maps, nplanes):
        rng = random.Random(1642 + q)
        dirs = q3.directions(q)
        tally = {"inv": 0, "b": 0, "c": 0, "residual": 0}
        for P in maps:
            planes = dirs if nplanes is None else rng.sample(dirs, nplanes)
            c = check_quad(self, q, P, planes)
            if c["inv"]:
                tally["inv"] += 1
            elif c["residual"]:
                tally["residual"] += 1
            elif c["cond_b"]:
                tally["b"] += 1
            else:
                tally["c"] += 1
        return tally

    def test_random_q3(self):
        rng = random.Random(3)
        maps = [rand_quad(rng, 3) for _ in range(150)]
        print("q = 3 random degree-2:", self.run_family(3, maps, None))

    def test_random_q5(self):
        rng = random.Random(5)
        maps = [rand_quad(rng, 5) for _ in range(40)]
        print("q = 5 random degree-2:", self.run_family(5, maps, 10))

    def test_random_q7(self):
        rng = random.Random(7)
        maps = [rand_quad(rng, 7) for _ in range(8)]
        print("q = 7 random degree-2:", self.run_family(7, maps, 4))

    def test_triangular(self):
        """Maps respecting span(e1) and span(e1, e2), in random bases: Theorem 40 (a)."""
        for q, reps, npl in ((3, 30, None), (5, 12, 6), (7, 3, 3)):
            rng = random.Random(100 + q)
            maps = []
            for _ in range(reps):
                P = q3.upper_triangular(q, [rng.randrange(q) for _ in range(27)])
                P = q3.conjugate(q, P, rand_gl3(rng, q))
                c = q3.classify(q, P)
                self.assertTrue(c["inv"])
                maps.append(P)
            print("q =", q, "triangular:", self.run_family(q, maps, npl))

    def test_type_b(self):
        """Section 4: every direction w with w1 = 0 lies on the cylinder locus Z."""
        for q, reps, npl in ((3, 20, None), (5, 12, 6), (7, 3, 3)):
            rng = random.Random(200 + q)
            maps = []
            for _ in range(reps):
                psi = [rng.randrange(q) for _ in range(6)]
                l1 = [rng.randrange(q) for _ in range(3)]
                P = q3.type_b(q, psi, l1, rng.randrange(q), rng.randrange(q),
                              rng.randrange(q))
                for w in q3.directions(q):
                    if w[0] == 0:
                        self.assertLessEqual(q3.rank_data(q, P, w)[2], 2, (q, w))
                maps.append(P)
            print("q =", q, "type (b):", self.run_family(q, maps, npl))

    def test_veronese(self):
        """Section 4: every direction (1, s, s^2) lies on Z when a - 2d + e = 0."""
        for q, reps, npl in ((3, 20, None), (5, 12, 6), (7, 3, 3)):
            rng = random.Random(300 + q)
            maps = []
            for _ in range(reps):
                P = q3.veronese(q, *[rng.randrange(q) for _ in range(4)])
                for s in range(q):
                    w = (1, s, s * s % q)
                    self.assertLessEqual(q3.rank_data(q, P, w)[2], 2, (q, w))
                maps.append(P)
            print("q =", q, "veronese:", self.run_family(q, maps, npl))


if __name__ == "__main__":
    unittest.main(verbosity=2)
