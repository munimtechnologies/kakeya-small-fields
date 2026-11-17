# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Tests for inverse_family.py (note a160, Theorem 36). Standard library only.
Run: python test_inverse_family.py  (or python -m unittest -v)."""
import math
import os
import sys
import unittest
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import inverse_family as IF  # noqa: E402
import lemma_l as LL  # noqa: E402


class TestQuadExt(unittest.TestCase):
    def test_field_axioms(self):
        for q in (4, 8):
            E = IF.QuadExt(q)
            R = range(E.N)
            one = E.join(1, 0)
            for x in R:
                self.assertEqual(E.mul(x, one), x)
                if x:
                    self.assertEqual(E.mul(x, E.inv0(x)), one, (q, x))
                    self.assertEqual(sorted(E.mul(x, z) for z in R), list(R))
            for x in range(0, E.N, 3):
                for z in range(0, E.N, 5):
                    for w in range(0, E.N, 7):
                        self.assertEqual(E.mul(E.mul(x, z), w), E.mul(x, E.mul(z, w)))
                        self.assertEqual(E.mul(x, E.add(z, w)), E.add(E.mul(x, z), E.mul(x, w)))
            self.assertEqual(E.inv0(0), 0)

    def test_q16_inverses(self):
        E = IF.QuadExt(16)
        one = E.join(1, 0)
        for x in range(1, E.N):
            self.assertEqual(E.mul(x, E.inv0(x)), one)

    def test_subfield_scalars_match_lemma_l(self):
        """Multiplying by t in F_q inside E is lemma_l's scalar multiplication."""
        for q in (4, 8, 16):
            E = IF.QuadExt(q)
            sp = LL.Space(q, 2)
            for t in range(q):
                for x in range(E.N):
                    self.assertEqual(E.mul(E.join(t, 0), x), sp.smul[t][x])
                    self.assertEqual(E.add(x, t), sp.vadd[x][t])


class TestTheorem36(unittest.TestCase):
    def check(self, q, s=None, gamma=None):
        r = IF.report(q, gamma=gamma, s=s)
        self.assertEqual(r["fibre_sizes"], [[2]] * q, (q, s))           # every Y_t is 2-to-1
        self.assertAlmostEqual(r["lambda"], q, places=9)                  # Lambda(P) = q
        self.assertEqual(r["same_l_pairs"], r["predicted_same_l_pairs"], (q, s))
        for n, lam_l in zip(r["same_l_pairs"], r["lambda_l"]):
            self.assertAlmostEqual(float(IF.exact_lambda_l(q, n)), lam_l, places=9)
        self.assertEqual(Fraction(r["min_lambda_l_exact"]),
                         Fraction(q - 1) + Fraction(q - 2, q * q))
        self.assertTrue(r["L_fails"])
        return r

    def test_q4_every_s(self):
        E = IF.QuadExt(4)
        n = 0
        for s in range(E.N):
            if not E.in_subfield(s):
                self.check(4, s=s)
                n += 1
        self.assertEqual(n, 12)

    def test_q8_every_s(self):
        E = IF.QuadExt(8)
        n = 0
        for s in range(E.N):
            if not E.in_subfield(s):
                self.check(8, s=s)
                n += 1
        self.assertEqual(n, 56)

    def test_q16(self):
        self.check(16)

    def test_q4_hand_example(self):
        """The example worked by hand in note a160: gamma = w (so y = a, a^4 + a + 1 = 0),
        s = y. Lambda_l = 7/2 for ker l = F_4 and 25/8 otherwise; the chain bound of
        Theorem 35 for l = x0, v = 1 is 5 + (9/16) log2 3 < 6, so L' holds for this map."""
        r = self.check(4, gamma=2, s=4)
        for f, lam_l in zip(r["functionals"], r["lambda_l"]):
            self.assertAlmostEqual(lam_l, 3.5 if f == [0, 1] else 25 / 8, places=9)
        E = IF.QuadExt(4, 2)
        P = IF.inverse_map(E, 4)
        # spot values from the hand table: P(y) = 1 + w y, P(1) = 1 + y, P(w^2 + w y) = 0
        self.assertEqual(P[E.join(0, 1)], E.join(1, 2))
        self.assertEqual(P[E.join(1, 0)], E.join(1, 1))
        self.assertEqual(P[E.join(3, 2)], 0)
        sp = LL.Space(4, 2)
        li = sp.funcs.index([1, 0])
        self.assertAlmostEqual(LL.chain_bound(sp, P, li, 1),
                               5 + 9 / 16 * math.log2(3), places=9)
        c, _, _ = LL.best_chain(sp, P)
        self.assertLessEqual(c, 6 + LL.TOL)

    def test_lines_partition_the_pairs(self):
        """Every colliding pair's difference lies on exactly one F_q-line, so the N_D add up
        to the q * q^2/2 colliding pairs."""
        for q in (4, 8, 16):
            funcs = [[0, 1]] + [[1, c] for c in range(q)]
            self.assertEqual(sum(IF.predicted_same_pairs(q, f) for f in funcs), q ** 3 // 2)

    def test_subfield_s_rejected(self):
        E = IF.QuadExt(4)
        with self.assertRaises(ValueError):
            IF.inverse_map(E, 3)


if __name__ == "__main__":
    res = unittest.main(exit=False, verbosity=2).result
    print("TESTS", "OK" if res.wasSuccessful() else "FAILED", flush=True)
    sys.exit(0 if res.wasSuccessful() else 1)
