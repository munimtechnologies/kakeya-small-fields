# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests for central_density.py: only values that are proved by hand are asserted."""
import unittest

from central_density import (centre, diagonal_matches_centre, element_order, least_power,
                             metacyclic, metacyclic_example, omega_bound_summary, quaternion,
                             quaternion_diagonal)


class TestQuaternion(unittest.TestCase):
    def test_involutions_central(self):
        for n in (3, 4, 5):
            elems, mul, one, _ = quaternion(n)
            involutions = {g for g in elems if element_order(mul, one, g) == 2}
            self.assertEqual(involutions, {(2 ** (n - 2), 0)})
            self.assertEqual(centre(quaternion(n)), frozenset([one, (2 ** (n - 2), 0)]))

    def test_diagonal_is_centre(self):
        # Proposition 15: lambda = log 2 / log 2^n, i.e. 1/n
        for n in (3, 4, 5):
            self.assertEqual(quaternion_diagonal(n), (2 ** n, 2))

    def test_prop15_on_every_subgroup(self):
        self.assertTrue(diagonal_matches_centre(quaternion(3)))
        self.assertTrue(diagonal_matches_centre(quaternion(4)))


class TestMetacyclic(unittest.TestCase):
    def test_sharp_example(self):
        # L = <y>, conjugated by x: only y^(p^(e-1)) survives, lambda = 1/e
        self.assertEqual(metacyclic_example(3, 2), (9, 3))
        self.assertEqual(metacyclic_example(3, 4), (81, 3))
        self.assertEqual(metacyclic_example(5, 2), (25, 5))

    def test_theorem16_small(self):
        s = omega_bound_summary(metacyclic(3, 2), 3, 2)
        self.assertEqual(s["order"], 81)
        self.assertTrue(s["order_p_central"])
        self.assertTrue(s["bound_holds"])
        self.assertAlmostEqual(s["least_ratio"], 0.5)


class TestLeastPowers(unittest.TestCase):
    def test_q16(self):
        # 2^(8 + 32m) < 2^(33m) iff m > 8; 2^(24 + 96m) < 2^(105m) iff m > 8/3
        self.assertEqual(least_power(16, 2, 2), 9)
        self.assertEqual(least_power(16, 2, 3), 3)

    def test_metacyclic_e4(self):
        # r = 2: 2^8 p^(32m) < p^(33m) iff p^m > 256
        self.assertEqual(least_power(3 ** 4, 3, 2), 6)
        self.assertEqual(least_power(5 ** 4, 5, 2), 4)
        self.assertEqual(least_power(7 ** 4, 7, 2), 3)

    def test_exponent_three_never_breaks_r2(self):
        # lambda = 1/3 exactly: |K| / |D|^(3/8) stays 2, so no m works
        self.assertIsNone(least_power(27, 3, 2, limit=60))


if __name__ == "__main__":
    unittest.main()
