# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests for theorem19.py: only values that are proved by hand are asserted."""
import unittest

from theorem19 import check_group, cyclic, direct_product, metacyclic, quaternion


class TestHypotheses(unittest.TestCase):
    def test_class_two_groups(self):
        for group in (quaternion(3), direct_product(quaternion(3), cyclic(4)), metacyclic(8, 8, 5)):
            s = check_group(group)
            self.assertTrue(s["class_le_2"])
            self.assertTrue(s["involutions_central"])

    def test_q16_is_class_three(self):
        s = check_group(quaternion(4))
        self.assertFalse(s["class_le_2"])
        self.assertTrue(s["involutions_central"])


class TestTheorem19(unittest.TestCase):
    def test_q8(self):
        s = check_group(quaternion(3))
        self.assertEqual(s["whole"], {"log2_order": 3, "e": 2, "k": 1, "a": {1: 1}, "bound": 3})
        self.assertTrue(s["bound_holds"])
        # Z_2, Z_4 and Q_8 itself are all equality cases
        self.assertEqual(s["equality_cases"], [(1, 1, 1), (2, 2, 1), (3, 2, 1)])

    def test_q8_x_z4_equality(self):
        s = check_group(direct_product(quaternion(3), cyclic(4)))
        self.assertEqual(s["whole"], {"log2_order": 5, "e": 2, "k": 2, "a": {1: 1, 2: 1}, "bound": 5})
        self.assertTrue(s["bound_holds"])

    def test_q8_x_z8_equality(self):
        s = check_group(direct_product(quaternion(3), cyclic(8)))
        self.assertEqual(s["whole"], {"log2_order": 6, "e": 3, "k": 2, "a": {1: 1, 3: 1}, "bound": 6})
        self.assertTrue(s["bound_holds"])

    def test_q8_squared_equality(self):
        s = check_group(direct_product(quaternion(3), quaternion(3)))
        self.assertEqual(s["whole"], {"log2_order": 6, "e": 2, "k": 2, "a": {1: 2}, "bound": 6})
        self.assertTrue(s["bound_holds"])

    def test_metacyclic_order_64(self):
        # <x, y | x^8 = y^8 = 1, y x y^(-1) = x^5>: Z = <x^2, y^2> = Z_4^2, bound 3*2 + 2 = 8
        s = check_group(metacyclic(8, 8, 5))
        self.assertEqual(s["whole"], {"log2_order": 6, "e": 3, "k": 2, "a": {2: 2}, "bound": 8})
        self.assertTrue(s["bound_holds"])

    def test_q16_needs_class_two(self):
        # Z(Q_16) = Z_2, e = 3: e k + a_2 = 3 < 4, but |Q_16| = |Omega_1|^(e+1) holds
        s = check_group(quaternion(4))
        self.assertEqual(s["whole"], {"log2_order": 4, "e": 3, "k": 1, "a": {1: 1}, "bound": 3})
        self.assertFalse(s["bound_holds"])
        self.assertTrue(s["omega_e_plus_1_holds"])


if __name__ == "__main__":
    unittest.main()
