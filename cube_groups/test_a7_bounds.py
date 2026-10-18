# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import a6_bounds as a6
import a7_bounds as a7


class TestTable(unittest.TestCase):
    def test_graded(self):
        tb = a7.table()
        self.assertTrue(all(tb["graded"].values()), tb["graded"])

    def test_newly_settled(self):
        tb = a7.table()
        self.assertEqual(tb["newly_settled"], [(10, 2), (10, 3), (13, 9), (14, 11)])
        self.assertEqual(tb["newly_settled_by_29_alone"], [(10, 2), (13, 9)])

    def test_first_open(self):
        fo = a7.table()["first_open"]
        self.assertEqual(fo, {"2": 11, "3": 11, "4": 11, "5": 12, "6": 12, "7": 13, "8": 13,
                              "9": 14, "10": 14, "11": None, "12": None})

    def test_by_hand(self):
        # Corollary 33 by hand: the reducible terms at t = 7, 8, 11, 12 are at most 8, 10, 18, 21,
        # below the caps 9 and 11 of Theorems 29 and 30 and below t + A(t - 4) = 20 and 23.
        A, E = a7.bounds(14)
        self.assertEqual(a7.reducible(7, A, E), 8)
        self.assertEqual(a7.reducible(8, A, E), 10)
        self.assertEqual(a7.reducible(11, A, E), 18)
        self.assertEqual(a7.reducible(12, A, E), 21)
        self.assertEqual((A[7], E[7], A[8], E[8]), (9, 2, 11, 3))
        self.assertEqual((A[11], E[11], A[12], E[12]), (20, 9, 23, 11))
        old_A, old_E = a6.bounds(14)
        self.assertEqual([t for t in range(15) if A[t] != old_A[t]], [7, 8, 11, 12])
        self.assertEqual([t for t in range(15) if E[t] != old_E[t]], [7, 8, 11, 12])

    def test_pairs(self):
        # b = 2: E(s) <= 2 for s <= 7 (E(7) = 2, was 3), so tau = 7 and (10 - 9)(1) = 1 <= 1.
        self.assertTrue(a7.settled(10, 2))
        self.assertFalse(a7.settled(11, 2))
        self.assertFalse(a6.settled(10, 2))
        # b = 3: E(8) = 3 (was 4) needs Theorem 30; then tau = 8 and (10 - 10)(2) = 0.
        self.assertTrue(a7.settled(10, 3))
        self.assertFalse(a7.settled(10, 3, upper={6: 7, 7: 9}))
        self.assertFalse(a7.settled(11, 3))
        # b = 9: E(11) = 9 (was 10), tau = 11, (13 - 13)(8) = 0.
        self.assertTrue(a7.settled(13, 9))
        self.assertFalse(a7.settled(14, 9))
        # b = 11: E(12) = 11 (was 12) needs Theorem 30; tau = 12, (14 - 14)(10) = 0.
        self.assertTrue(a7.settled(14, 11))
        self.assertFalse(a7.settled(14, 11, upper={6: 7, 7: 9}))


if __name__ == "__main__":
    unittest.main()
