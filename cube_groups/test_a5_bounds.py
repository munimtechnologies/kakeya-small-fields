# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

try:
    import a5_bounds as ab
except ImportError:
    from cube_groups import a5_bounds as ab


class TestCore(unittest.TestCase):
    def test_helpers(self):
        self.assertEqual(sum(1 for r in ab.RANK3 if r <= 1), 50)
        self.assertEqual(sum(1 for r in ab.RANK3 if r == 3), 168)
        ident = 1 | 1 << 4 | 1 << 8
        self.assertEqual([ab.apply3(ident, x) for x in range(8)], list(range(8)))
        self.assertEqual(ab.kernel(ident), [])
        self.assertEqual(len(ab.kernel(0)), 7)

    def test_d1(self):
        # 49 rank-1 matrices x f; x f + y g has rank 2 iff x != y and f != g: 49 * 36 pairs.
        self.assertEqual(ab.core_d1(1), (1764, 0))

    def test_d2(self):
        # 49 matrices of rank 1, each with 3 x 2 ordered pairs (x0, z) in its kernel.
        self.assertEqual(ab.core_d2(1), (294, 0))

    def test_control(self):
        self.assertGreater(ab.core_d1(2)[1], 0)
        self.assertGreater(ab.core_d2(2)[1], 0)


class TestTable(unittest.TestCase):
    def test_bounds(self):
        self.assertEqual(ab.bounds(12), ([0, 1, 2, 3, 4, 5, 8, 10, 12, 14, 18, 21, 24],
                                         [0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 8, 10, 12]))

    def test_table(self):
        out = ab.table()
        self.assertTrue(all(out["graded"].values()))
        self.assertEqual(out["newly_settled"], [(11, 5)])
        self.assertEqual({b: out["first_open"][str(b)] for b in range(2, 12)},
                         {2: 10, 3: 10, 4: 11, 5: 12, 6: 12, 7: 12, 8: 13, 9: 13, 10: 14, 11: 14})
        self.assertTrue(ab.settled(11, 5))
        self.assertFalse(ab.settled(11, 5, known=4))
        for a, b in ((10, 2), (10, 3), (11, 4), (12, 5), (12, 6), (14, 10), (14, 11)):
            self.assertFalse(ab.settled(a, b))


if __name__ == "__main__":
    unittest.main()
