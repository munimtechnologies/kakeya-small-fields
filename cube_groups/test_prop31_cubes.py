# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

from prop31_cubes import (agl_contrast, check, generated, groups, inverses, left_cosets,
                          normal_subgroups, served)


class TestGroups(unittest.TestCase):
    def test_orders_and_identity(self):
        orders = {"S_3": 6, "D_4": 8, "Q_8": 8, "A_4": 12, "AGL(1,5)": 20}
        for name, T in groups().items():
            self.assertEqual(len(T), orders[name])
            self.assertEqual(T[0], list(range(len(T))))
            inv = inverses(T)
            self.assertTrue(all(T[x][inv[x]] == 0 for x in range(len(T))))

    def test_associative(self):
        for T in groups().values():
            n = len(T)
            self.assertTrue(all(T[T[a][b]][c] == T[a][T[b][c]]
                                for a in range(n) for b in range(n) for c in range(n)))

    def test_normal_subgroup_counts(self):
        counts = {"S_3": 3, "D_4": 6, "Q_8": 6, "A_4": 3, "AGL(1,5)": 4}
        for name, T in groups().items():
            self.assertEqual(len(normal_subgroups(T)), counts[name], name)

    def test_cosets_partition(self):
        T = groups()["A_4"]
        for L in normal_subgroups(T):
            cosets = left_cosets(T, L)
            self.assertEqual(sum(len(c) for c in cosets), 12)
            self.assertEqual(len(cosets) * len(L), 12)


class TestProposition(unittest.TestCase):
    def test_s3_equality(self):
        T = groups()["S_3"]
        A3 = next(L for L in normal_subgroups(T) if len(L) == 3)
        self.assertEqual(len(served(T, A3, 2, 1, A3)), 9)          # = |K|^2

    def test_whole_group_equality(self):
        T = groups()["Q_8"]
        G = frozenset(range(8))
        self.assertEqual(len(served(T, G, 2, 0, G)), 64)

    def test_no_violations_small(self):
        for name in ("S_3", "Q_8", "D_4"):
            T = groups()[name]
            for r, cap in ((1, 8), (2, 8), (3, 4)):
                checked, violations, equal, worst = check(T, r, cap, limit=200)
                self.assertGreater(checked, 0)
                self.assertEqual(violations, [], (name, r))
                self.assertLessEqual(worst, 1.0)

    def test_non_normal_contrast(self):
        T = groups()["AGL(1,5)"]
        L = generated(T, (1,))
        self.assertEqual(len(L), 4)
        self.assertFalse(L in normal_subgroups(T))
        self.assertEqual(agl_contrast(), (80, 64))


if __name__ == "__main__":
    unittest.main()
