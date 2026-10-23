# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a83_targets.py: the pairs of notes/a83.md, and the configuration counts, with
Proposition 29 (t = 7, dim V = 9) and the configurations behind Theorem 31 (t = 6, dim V = 7) as
controls."""
import unittest

import a80_bounds as ab
import a83_targets as tg


class TestTargets(unittest.TestCase):
    def test_baseline(self):
        self.assertEqual(tg.newly_settled({}), [])
        self.assertTrue(all(ab.table()["graded"].values()))

    def test_targets(self):
        self.assertEqual(tg.newly_settled({7: 7}), [(13, 7)])
        self.assertEqual(tg.newly_settled({8: 10}), [(11, 2), (14, 10)])
        self.assertEqual(tg.newly_settled({9: 12}), [(11, 3), (15, 12)])
        self.assertEqual(tg.newly_settled({7: 7, 8: 10}), [(11, 2), (13, 7), (14, 10)])

    def test_controls(self):
        # Theorem 31's setting: rank 4 in Case A or B, rank 3 in (A4), (B4), (B5).
        self.assertEqual(tg.reduction(6, 7),
                         {3: [("A", 5, 3), ("B", 4, 3), ("B", 5, 2)],
                          4: [("A", 6, 2), ("B", 5, 2)]})
        # Proposition 29: rank 4 in Case A or B, rank 3 in (A5), (B5), (B6).
        self.assertEqual(tg.reduction(7, 9),
                         {3: [("A", 6, 4), ("B", 5, 4), ("B", 6, 3)],
                          4: [("A", 7, 3), ("B", 6, 3)]})
        # Theorem 33 leaves nothing at dim V = 10 to count: A(7) <= 9 is Theorem 29.
        self.assertEqual(tg.reduction(7, 10), {3: [("B", 6, 4)]})
        self.assertIsNone(tg.reduction(7, 7))

    def test_new(self):
        self.assertEqual(tg.reduction(8, 11), {3: [("B", 6, 5), ("B", 7, 4)], 4: [("B", 7, 4)]})
        self.assertEqual(tg.reduction(9, 13), {3: [("B", 7, 6), ("B", 8, 5)], 4: [("B", 8, 5)]})
        r = tg.reduction(7, 8)
        self.assertEqual(sorted(r), [3, 4, 5])
        self.assertEqual(r[5], [("A", 7, 2), ("B", 6, 2)])
        self.assertEqual(r[4], [("A", 6, 3), ("A", 7, 2), ("B", 5, 3), ("B", 6, 2)])
        self.assertEqual(r[3], [("A", 5, 4), ("A", 6, 3), ("B", 4, 4), ("B", 5, 3), ("B", 6, 2)])
        self.assertEqual(sum(len(v) for v in r.values()), 11)


if __name__ == "__main__":
    unittest.main()
