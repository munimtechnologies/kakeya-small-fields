# SPDX-License-Identifier: Apache-2.0
"""Tests for pencils3.py (note a165: Theorem 41, Proposition 49).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only. Every assertion is a fact proved by hand in a165 (or in a164),
so a failure means a bug in the code or an error in the hand proof. The commit carrying
a165 ships only if all pass.
"""

import math
import unittest
from collections import Counter

import pencils3 as p3

SMALL = (3, 5)
Q7_PARAMS = ((0, 0), (1, 0), (0, 1), (2, 5), (3, 0), (3, 1))  # (rho, delta) at q = 7


def params(q):
    for rho in range(q):
        for delta in range(q):
            yield rho, delta


def is_exceptional(q, rho, delta):
    return (2 * rho + 1) % q == 0 and delta % q == 0


class TestFamily(unittest.TestCase):

    def check_map(self, q, rho, delta):
        P = p3.family(q, rho, delta)
        exc = is_exceptional(q, rho, delta)
        # Theorem 41 (i): the two type-(b) structures, with ker m1 != ker m2
        s1, s2 = p3.structures(q, rho, delta)
        self.assertTrue(p3.has_structure(q, P, s1), (q, rho, delta, "S1"))
        self.assertTrue(p3.has_structure(q, P, s2), (q, rho, delta, "S2"))
        # Theorem 41 (ii): no invariant line or plane
        self.assertEqual(p3.invariant_lines(q, P), [], (q, rho, delta))
        self.assertEqual(p3.invariant_planes(q, P), [], (q, rho, delta))
        # Theorem 41 (iii): the cylinder set D (rank form and brute-force witness form)
        pred = p3.predicted_D(q, exc)
        self.assertEqual(p3.cylinder_set(q, P), pred, (q, rho, delta))
        self.assertEqual(p3.witness_set(q, P), pred, (q, rho, delta))
        self.assertEqual(len(pred), 3 * q if exc else 2 * q + 1)
        # Theorem 40 (c) of a164 applies to every non-exceptional member
        if not exc:
            self.assertLessEqual((q - 1) * len(pred), (2 * q + 1) * (q - 1))
        # Conjecture C_q(3) for the whole family (Thm 40 (c), and Prop 49 for E)
        self.assertLessEqual(p3.score_int(q, P), p3.bound_int(q), (q, rho, delta))
        return P, exc

    def test_all_small(self):
        for q in SMALL:
            n_exc = 0
            for rho, delta in params(q):
                _, exc = self.check_map(q, rho, delta)
                n_exc += exc
            self.assertEqual(n_exc, 1)

    def test_some_q7(self):
        q = 7
        for rho, delta in Q7_PARAMS:
            _, exc = self.check_map(q, rho, delta)
            self.assertEqual(exc, rho == 3 and delta == 0)


class TestExceptional(unittest.TestCase):

    def test_residual_and_exact(self):
        for q in (3, 5, 7):
            E = p3.exceptional(q)
            self.assertEqual(E, p3.family(q, (q - 1) * p3.half(q) % q, 0))
            # first coordinate in factored form
            h = p3.half(q)
            for i, x in enumerate(p3.points(q)):
                x1, x2, x3 = x
                f1 = ((2 * x1 + x2) * x3 - h * (3 * x1 + x2) * (x1 + x2)) % q
                self.assertEqual(E[i][0], f1)
            D = p3.cylinder_set(q, E)
            pis = {w: p3.pi_w(q, E, w) for w in p3.directions(q)}
            Z0 = [w for w, v in pis.items() if v == 0]
            self.assertEqual(Z0, [])
            # Prop 47 of a164: Pi_w = (q-1) q^(3 - r_w), r_w = 1 on D and 2 elsewhere
            for w, v in pis.items():
                self.assertEqual(v, (q - 1) * q ** (2 if w in D else 1), (q, w))
            # E is in the residual case of Theorem 40: neither (b) nor (c) holds
            cond_b, cond_c = p3.theorem40_conditions(q, D, Z0)
            self.assertFalse(cond_b, q)
            self.assertFalse(cond_c, q)
            # ... and the pair-count bound of a164 exceeds 3(q-1) on E
            self.assertGreater(sum(pis.values()), 3 * (q - 1) * q ** 3)
            # Proposition 49: the same fibre histogram for every t, exact Lambda
            want = p3.predicted_hist_E(q)
            for t in range(q):
                self.assertEqual(Counter(p3.fibre_sizes(q, E, t)), want, (q, t))
            self.assertEqual(p3.score_int(q, E), p3.predicted_score_E(q))
            self.assertLess(p3.predicted_score_E(q), p3.bound_int(q))

    def test_formula_below_bound(self):
        # Proposition 49: Lambda(E) < 3(q-1) for every odd q (checked exactly up to 199;
        # for q >= 7 the hand bound 3 log2 q + 3 log2(3q)/q <= 2(q-1) covers the rest)
        for q in range(3, 200, 2):
            self.assertLess(p3.lam_E_float(q), 3 * (q - 1) - 1e-9, q)
            self.assertLess(p3.lam_E_float(q), q + 3 * math.log2(3 * q), q)


if __name__ == "__main__":
    unittest.main()
