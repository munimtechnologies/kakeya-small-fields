"""Tests for z4degree.py. By MV2 of Munim, Inc. Licence: Apache-2.0."""

import unittest

import z4degree as z


class TestHelpers(unittest.TestCase):
    def test_det(self):
        self.assertEqual(z.det2(((1, 0, 0), (0, 1, 0), (0, 0, 1))), 1)
        self.assertEqual(z.det2(((1, 1), (1, 1))), 0)
        self.assertEqual(z.det2(((0, 1), (1, 1))), 1)
        self.assertEqual(z.det2(((1, 1), (1, 0))), 1)

    def test_anf_degree(self):
        n = 3
        self.assertEqual(z.anf_degree([1] + [0] * 7, n), 3)        # delta_0
        self.assertEqual(z.anf_degree([0] * 8, n), -1)
        self.assertEqual(z.anf_degree([int(x & 3 == 3) for x in range(8)], n), 2)  # x0 x1
        self.assertEqual(z.anf_degree([bin(x).count("1") % 2 for x in range(8)], n), 1)

    def test_groups_are_groups(self):
        for name, (E, mul, A), _ in z.groups()[:3] + z.groups()[6:]:
            e = z.identity_of(E, mul)
            for x in E:
                self.assertTrue(any(mul(x, y) == e for y in E), name)


class TestSmallGroups(unittest.TestCase):
    def test_q8(self):
        r = z.analyze(*z.q8())
        self.assertEqual((r["order"], r["k"], r["n"]), (8, 1, 1))
        self.assertTrue(r["all_involutions_central"] and r["self_centralising"])
        self.assertEqual(r["sigma_nonzero_cosets"], 0)
        self.assertTrue(r["det_is_delta0"] and r["lemma22d_criterion"])
        self.assertEqual(r["det_degree"], 1)

    def test_p32(self):
        r = z.analyze(*z.p32())
        self.assertTrue(r["associative"] and r["A_is_Z4k"] and r["normal"])
        self.assertEqual((r["order"], r["k"], r["n"]), (32, 2, 1))
        self.assertTrue(r["all_involutions_central"] and r["omega_is_2A"])
        self.assertEqual(r["sigma_nonzero_cosets"], 1)      # exponent 8: e = 3
        self.assertTrue(r["M_sigma_zero"] and r["det_is_delta0"])

    def test_control_irreducible(self):
        r = z.analyze(*z.z4sq_z2())
        self.assertFalse(r["all_involutions_central"])
        self.assertFalse(r["det_is_delta0"])
        self.assertTrue(r["lemma22d_criterion"])

    def test_control_d8(self):
        r = z.analyze(*z.d8())
        self.assertFalse(r["all_involutions_central"])
        self.assertTrue(r["det_is_delta0"])
        self.assertTrue(r["lemma22d_criterion"])

    def test_q8_squared(self):
        Q = z.q8()
        r = z.analyze(*z.product(Q, Q))
        self.assertEqual((r["order"], r["k"], r["n"]), (64, 2, 2))
        self.assertTrue(r["det_is_delta0"] and r["M_additive"] and r["M_injective"])
        self.assertEqual(r["det_degree"], 2)


if __name__ == "__main__":
    unittest.main()
