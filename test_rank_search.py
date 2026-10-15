"""Exhaustive check of Proposition 2 (README section 10): every f : F_3^2 -> F_3 (3^9 = 19,683
functions) and every f : F_2^2 -> F_2. Pure Python, a few seconds.
By MV2 of Munim, Inc.; researched and written with AI agents working in MV2's name.
Code Apache-2.0."""
import math
import unittest

from higher_rank import phi_norm, phi_square, phi_zero, search


class Exhaustive(unittest.TestCase):
    def test_every_f_on_F3_squared(self):
        result = search(3, 2)
        msg = str(result)
        self.assertEqual(result["functions"], 19683)
        # the best one-coordinate witness is the square of one coordinate
        self.assertAlmostEqual(result["min_phi"], math.log2(3) - 2 / 9, places=9, msg=msg)
        self.assertAlmostEqual(result["min_phi"], phi_square(3, 2), places=9, msg=msg)
        # among the f whose nine slices all take all three values, the norm form is best
        self.assertAlmostEqual(result["min_phi_all_values"], phi_norm(3, 2), places=9, msg=msg)
        # at most three slices miss a value, and three only when f is affine along a line
        self.assertEqual(result["most_missing_slices"], 3, msg=msg)
        self.assertTrue(result["three_missing_means_one_direction"], msg=msg)

    def test_every_f_on_F2_squared(self):
        # q = r = 2: nothing beats f = 0, which is KLSS's 2^(3n/4)
        result = search(2, 2)
        msg = str(result)
        self.assertEqual(result["functions"], 16)
        self.assertAlmostEqual(result["min_phi"], 0.75, places=12, msg=msg)
        self.assertAlmostEqual(result["min_phi"], phi_zero(2, 2), places=12, msg=msg)
        self.assertAlmostEqual(result["min_phi_all_values"], phi_norm(2, 2), places=12, msg=msg)
        self.assertEqual(result["most_missing_slices"], 1, msg=msg)


if __name__ == "__main__":
    unittest.main()
