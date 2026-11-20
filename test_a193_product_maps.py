# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name; no human has checked this.
"""Tests for note a193 (Proposition 87, Observation 87.1)."""
import unittest

import a193_product_maps as m


class TestA193(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.res = m.run()

    def test_lines_and_frames(self):
        self.assertEqual(self.res["lines"], 13)
        self.assertEqual(self.res["frames"], 234)

    def test_product_maps_distinct(self):
        # 234 frames * 8 sign patterns * 27 linear diagonals, all distinct
        self.assertEqual(self.res["parameter_choices"], 50544)
        self.assertEqual(self.res["distinct_maps"], 50544)
        self.assertEqual(self.res["max_multiplicity"], 1)

    def test_every_product_map_has_S_162(self):
        self.assertEqual(self.res["maps_with_S_162"], 50544)
        self.assertEqual(self.res["S_values"], [162.0])
        self.assertEqual(self.res["maps_with_P0_zero"], 50544)

    def test_per_class_counts_match_a192(self):
        per = self.res["per_L"]
        self.assertEqual(per["L=0"], 1872)
        self.assertEqual(per["L=I"], 1872)
        self.assertEqual(per["L=diag(1,0,0)"], 48)
        self.assertEqual(per["L=diag(2,0,0)"], 48)
        self.assertEqual(per["L=diag(0,1,2)"], 8)
        self.assertEqual(per["L=[[1,1,0],[0,1,0],[0,0,0]] (not diagonalisable)"], 0)
        # 3 scalar + 702 two-eigenvalue + 1404 three-eigenvalue diagonalisable matrices
        self.assertEqual(self.res["distinct_linear_parts"], 2109)

    def test_sticky_shape(self):
        self.assertEqual(self.res["sticky_G_slice_sizes"], [8, 8, 8])
        self.assertEqual(self.res["sticky_G_column_profiles"], [[2, 6]] * 3)
        self.assertEqual(self.res["classical_slice_sizes"], [8, 8, 8])
        self.assertEqual(self.res["classical_column_profiles"], [[4, 4]] * 3)


if __name__ == "__main__":
    unittest.main()
