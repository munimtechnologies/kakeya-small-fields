"""Tests for z4z2.py (Theorem 39 checks). By MV2 of Munim, Inc. Licence: Apache-2.0."""

import unittest

from z4z2 import analyze, anf_degree, det2, inverse2, matmul, product, q8, z2, z4sq_z2, z4z4


class LinearAlgebra(unittest.TestCase):
    def test_inverse(self):
        M = ((1, 1, 0), (0, 1, 1), (0, 0, 1))
        I = tuple(tuple(int(r == c) for c in range(3)) for r in range(3))
        self.assertEqual(matmul(M, inverse2(M)), I)

    def test_det(self):
        self.assertEqual(det2(((1, 1), (1, 0))), 1)
        self.assertEqual(det2(((1, 1), (1, 1))), 0)

    def test_anf(self):
        self.assertEqual(anf_degree([1, 0, 0, 0], 2), 2)      # indicator of 0
        self.assertEqual(anf_degree([0, 1, 1, 0], 2), 1)      # x_1 + x_2
        self.assertEqual(anf_degree([0, 0, 0, 0], 2), -1)


class SmallGroups(unittest.TestCase):
    def run_group(self, G):
        E, mul, A4, A2 = G
        return analyze(E, mul, A4, A2)

    def test_q8_x_z2(self):
        r = self.run_group(product(q8(), z2()))
        self.assertTrue(r["theorem39_consistent"])
        self.assertEqual((r["a"], r["b"], r["n"], r["n0"], r["rank_Q"], r["s"]), (1, 1, 1, 1, 0, 0))

    def test_z4z4_q_zero(self):
        r = self.run_group(z4z4(False))
        self.assertTrue(r["theorem39_consistent"])
        self.assertEqual(r["rank_Q"], 0)

    def test_z4z4_q_nonzero(self):
        r = self.run_group(z4z4(True))
        self.assertTrue(r["theorem39_consistent"])
        self.assertEqual((r["n"], r["n0"], r["rank_Q"]), (1, 0, 1))

    def test_q8_x_z4z4_swapped(self):
        r = self.run_group(product(q8(), z4z4(True)))
        self.assertTrue(r["theorem39_consistent"])
        self.assertEqual((r["a"], r["b"], r["n"], r["n0"], r["rank_Q"]), (2, 1, 2, 1, 1))

    def test_control_fails(self):
        r = self.run_group(product(z4sq_z2(), z2()))
        self.assertFalse(r["all_involutions_central"])
        self.assertFalse(r["F_is_indicator_on_H0"])
        self.assertFalse(r["theorem39_consistent"])


if __name__ == "__main__":
    unittest.main()
