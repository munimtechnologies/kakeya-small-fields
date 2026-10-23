# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import a80_bounds as a80


class TestTable(unittest.TestCase):
    def test_graded(self):
        tb = a80.table()
        self.assertTrue(all(tb["graded"].values()), tb["graded"])

    def test_newly_settled(self):
        self.assertEqual(a80.table()["newly_settled"], [(13, 8)])

    def test_first_open(self):
        fo = a80.table()["first_open"]
        self.assertEqual(fo, {"2": 11, "3": 11, "4": 12, "5": 12, "6": 13, "7": 13, "8": 14,
                              "9": 14, "10": 14, "11": None, "12": None})

    def test_by_hand(self):
        # Corollary 119 by hand: the reducible terms at t = 6, 7, 8, 9, 10, 11, 12 are at most
        # 6, 7, 9, 12, 14, 17, 20, below the caps 6, 8, 11, 13 of Theorems 31, 33, 30, 32 and
        # below t + A(t - 4) = 16, 19, 23 for t = 10, 11, 12.
        A, E = a80.bounds(14)
        self.assertEqual([a80.reducible(t, A, E) for t in range(6, 13)],
                         [6, 7, 9, 12, 14, 17, 20])
        self.assertEqual((A[7], E[7], A[11], E[11], A[12], E[12]), (8, 1, 19, 8, 23, 11))
        old_A, old_E = a80.bounds(14, upper=a80.UPPER_A23)
        self.assertEqual([t for t in range(15) if A[t] != old_A[t]], [7, 11])
        self.assertEqual([t for t in range(15) if E[t] != old_E[t]], [7, 11])

    def test_pairs(self):
        # b = 8: E(s) <= 8 for s <= 11 (E(11) = 8, was 9), E(12) = 11, so tau = 11 and
        # (13 - 13)(7) = 0.
        self.assertTrue(a80.settled(13, 8))
        self.assertFalse(a80.settled(13, 8, upper=a80.UPPER_A23))
        self.assertFalse(a80.settled(14, 8))
        # b = 7: E(11) = 8 still exceeds it, so tau stays 10.
        self.assertFalse(a80.settled(13, 7))
        # b = 2 and b = 3 do not move: E(8) = 3 and E(9) = 4 still exceed them.
        self.assertFalse(a80.settled(11, 2))
        self.assertFalse(a80.settled(11, 3))


if __name__ == "__main__":
    unittest.main()
