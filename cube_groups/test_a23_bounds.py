# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import a23_bounds as a23


class TestTable(unittest.TestCase):
    def test_graded(self):
        tb = a23.table()
        self.assertTrue(all(tb["graded"].values()), tb["graded"])

    def test_newly_settled(self):
        tb = a23.table()
        self.assertEqual(tb["newly_settled"], [(11, 4), (12, 6)])
        self.assertEqual(tb["newly_settled_by_31_alone"], [(12, 6)])

    def test_first_open(self):
        fo = a23.table()["first_open"]
        self.assertEqual(fo, {"2": 11, "3": 11, "4": 12, "5": 12, "6": 13, "7": 13, "8": 13,
                              "9": 14, "10": 14, "11": None, "12": None})

    def test_by_hand(self):
        # Corollary 49 by hand: the reducible terms at t = 6, 7, 8, 9, 10, 11, 12 are at most
        # 6, 7, 10, 12, 14, 17, 21, below the caps 6, 9, 11, 13 of Theorems 31, 29, 30, 32 and
        # below t + A(t - 4) = 16, 20, 23 for t = 10, 11, 12.
        A, E = a23.bounds(14)
        self.assertEqual([a23.reducible(t, A, E) for t in range(6, 13)],
                         [6, 7, 10, 12, 14, 17, 21])
        self.assertEqual((A[6], E[6], A[9], E[9], A[10], E[10]), (6, 0, 13, 4, 16, 6))
        old_A, old_E = a23.bounds(14, upper=a23.UPPER_A7)
        self.assertEqual([t for t in range(15) if A[t] != old_A[t]], [6, 9, 10])
        self.assertEqual([t for t in range(15) if E[t] != old_E[t]], [6, 9, 10])
        # Without Theorem 32: A(9) <= 9 + A(5) = 14, E(9) = 5, and still A(10) <= 10 + A(6) = 16.
        A31, E31 = a23.bounds(14, upper=a23.UPPER_31_ONLY)
        self.assertEqual((A31[9], E31[9], A31[10], E31[10]), (14, 5, 16, 6))

    def test_pairs(self):
        # b = 6: E(s) <= 6 for s <= 10 (E(10) = 6, was 7), so tau = 10 and (12 - 12)(5) = 0.
        self.assertTrue(a23.settled(12, 6))
        self.assertTrue(a23.settled(12, 6, upper=a23.UPPER_31_ONLY))
        self.assertFalse(a23.settled(12, 6, upper=a23.UPPER_A7))
        self.assertFalse(a23.settled(13, 6))
        # b = 4: E(9) = 4 (was 5) needs Theorem 32; then tau = 9 and (11 - 11)(3) = 0.
        self.assertTrue(a23.settled(11, 4))
        self.assertFalse(a23.settled(11, 4, upper=a23.UPPER_31_ONLY))
        self.assertFalse(a23.settled(12, 4))
        # b = 2 and b = 3 do not move: E(8) = 3 and E(9) = 4 still exceed them.
        self.assertFalse(a23.settled(11, 2))
        self.assertFalse(a23.settled(11, 3))


if __name__ == "__main__":
    unittest.main()
