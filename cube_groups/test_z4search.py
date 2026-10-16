"""Tests for z4search.py. By MV2 of Munim, Inc. Licence: Apache-2.0."""

import unittest

import z4search as z


class TestBasics(unittest.TestCase):
    def test_gl3_order(self):
        self.assertEqual(len(z.gl(3)), 168)

    def test_matmul_identity(self):
        I = z.identity(3)
        for M in (0, 5, 77, 300, 511):
            self.assertEqual(z.matmul(I, M, 3), M)
            self.assertEqual(z.matmul(M, I, 3), M)

    def test_orbits_cover_all_planes(self):
        reps = z.orbit_reps(3)
        self.assertEqual(sum(s for _, s in reps), 511 * 510 // 6)
        for W, _ in reps[:5]:
            self.assertEqual(len(z.perp_basis(W, 3)), 7)


class TestKnownGroups(unittest.TestCase):
    def test_q8_k1_has_no_order_8(self):
        # Q_8: A = Z_4, M = 1; sigma(h) = 0 is forced, so e <= 2
        r = z.analyze(1, [1])
        self.assertEqual(r["nullity"], 0)
        self.assertTrue(r["sigma0_ok"])
        self.assertFalse(r["e3"])

    def test_q8_powers_pass_with_sigma_zero(self):
        for k, basis in ((2, [1, 8]), (3, [1, 16, 256])):
            r = z.analyze(k, basis)
            self.assertTrue(r["sigma0_ok"])
            self.assertFalse(r["eigen_killed"])

    def test_order_8_example_k2(self):
        # A = <a> x <b> = Z_4^2, g^2 = a, g b g^-1 = b a^2: M e_b = e_a, sigma(g) = e_a
        r = z.analyze(2, [2])
        self.assertTrue(r["e3"])
        self.assertEqual(r["witness"]["sigma_basis"], [1])


class TestSolver(unittest.TestCase):
    def test_nullspace_solves_equations(self):
        reps = z.orbit_reps(3)
        for W, _ in reps[:6]:
            V = z.perp_basis(W, 3)
            nv = z.forms(7, 3)[0]
            piv = {}
            for e in z.equations(3, z.span_table(V), 7):
                z.insert(piv, e)
            rank = len(piv)
            null = z.nullspace(piv, nv)
            self.assertEqual(rank + len(null), nv)
            for x in null:
                self.assertTrue(z.check_solution(3, V, x))

    def test_eigen_filter_consistent(self):
        reps = z.orbit_reps(3)
        for W, _ in reps[:12]:
            r = z.analyze(3, z.perp_basis(W, 3))
            self.assertFalse(r["eigen_killed"] and r["e3"] is True)


if __name__ == "__main__":
    unittest.main()
