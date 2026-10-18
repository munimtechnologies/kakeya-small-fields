# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import a5_bounds as a5
import a6_bounds as a6


class TestTable(unittest.TestCase):
    def test_graded(self):
        tb = a6.table()
        self.assertTrue(all(tb["graded"].values()), tb["graded"])

    def test_newly_settled(self):
        self.assertEqual(a6.table()["newly_settled"], [(12, 7)])

    def test_first_open(self):
        fo = a6.table()["first_open"]
        self.assertEqual(fo, {"2": 10, "3": 10, "4": 11, "5": 12, "6": 12, "7": 13, "8": 13,
                              "9": 13, "10": 14, "11": 14, "12": None})

    def test_by_hand(self):
        # Corollary 29 by hand: only t + A(t - 4) moves, at t = 10 (10 + 7 = 17), and at t = 14
        # where 2t = 28 caps it anyway; the reducible terms stay below.
        A, E = a6.bounds(14)
        self.assertEqual(A[6], 7)
        self.assertEqual(E[6], 1)
        self.assertEqual(max(10 - d + E[10 - d] + A[d] for d in range(1, 10)), 15)
        self.assertEqual(A[10], 17)
        self.assertEqual(E[10], 7)
        old_A, old_E = a5.bounds(14)
        self.assertEqual([t for t in range(15) if A[t] != old_A[t]], [6, 10])
        self.assertEqual([t for t in range(15) if E[t] != old_E[t]], [6, 10])

    def test_pair_12_7(self):
        # b = 7: E(s) <= 7 for s <= 10 (E(10) = 7, was 8), E(11) = 10, so tau = 10 and
        # (12 - 10 - 2)(7 - 1) = 0 <= 1; (13, 7) gives (13 - 12)(6) = 6 > 1.
        self.assertTrue(a6.settled(12, 7))
        self.assertFalse(a6.settled(13, 7))
        self.assertFalse(a5.settled(12, 7))


if __name__ == "__main__":
    unittest.main()
