# Tests for sticky_break.py (note a187). MV2 of Munim, Inc. Made with AI agents. Apache-2.0.
import itertools
import json
import os
import unittest

from sticky_planes import kakeya_set, is_kakeya, slices, classical_maps
import sticky_break as sb

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results", "sticky_break.json")


class TestPieces(unittest.TestCase):
    def test_families_are_full_and_sticky(self):
        self.assertTrue(sb.is_full_family(sb.MAPS_K2, 2))
        for m in (sb.MAPS_Y, sb.MAPS_X, sb.MAPS_Z):
            self.assertTrue(sb.is_full_family(m, 2))
        self.assertTrue(sb.is_full_family(sb.tree_T(), 3))
        self.assertTrue(sb.is_full_family(sb.family_K3(), 3))
        self.assertTrue(sb.is_full_family(sb.family_K4(), 4))

    def test_height2_slices(self):
        row0 = {(0, b) for b in range(3)}
        row1 = {(1, b) for b in range(3)}
        graph0 = {(a, 0) for a in range(3)}
        plane = {(a, b) for a in range(3) for b in range(3)}
        self.assertEqual(slices(sb.MAPS_Y, 2), [graph0, row0, plane])
        self.assertEqual(slices(sb.MAPS_X, 2), [row1, graph0, plane])
        SZ = slices(sb.MAPS_Z, 2)
        self.assertEqual(SZ[0], row1 | {(0, 0)})
        self.assertEqual(SZ[1], row0 | {(2, 0)})
        self.assertEqual(SZ[2], row0 | {(2, 0)})

    def test_tree_T(self):
        S = slices(sb.tree_T(), 3)
        self.assertEqual([len(s) for s in S], [7, 7, 13])
        self.assertEqual(tuple(sb.game_vector(sb.tree_T(), 3)), (7, 7, 13))

    def test_K3(self):
        K3 = kakeya_set(sb.family_K3(), 3)
        self.assertEqual(len(K3), 15)
        self.assertTrue(is_kakeya(K3, 3))
        S2 = slices(sb.tree_T(), 3)[2]
        self.assertEqual(len(K3 | S2), 16)


class TestThirty(unittest.TestCase):
    def test_size_and_kakeya(self):
        K4 = kakeya_set(sb.family_K4(), 4)
        self.assertEqual(len(K4), 30)
        self.assertTrue(is_kakeya(K4, 4))
        self.assertEqual(len(kakeya_set(classical_maps(4), 4)), 31)

    def test_theorem74_formula(self):
        self.assertEqual(sb.formula_size(sb.family_K3(), sb.tree_T(), 2, (0, 0, 0), 3), 30)

    def test_planes(self):
        K4 = kakeya_set(sb.family_K4(), 4)
        self.assertEqual([sum(1 for p in K4 if p[0] == u) for u in range(3)], [16, 7, 7])

    def test_every_direction_has_its_own_line(self):
        maps = sb.family_K4()
        K4 = kakeya_set(maps, 4)
        for d in itertools.product(range(3), repeat=4):
            if not any(d):
                continue
            for q in sb.line_points(maps, d):
                self.assertIn(q, K4)


class TestColouringAndLift(unittest.TestCase):
    def test_colouring_is_good(self):
        self.assertTrue(sb.is_good_colouring(sb.family_K4(), 4, sb.colouring_K4()))

    def test_label_for_every_pattern(self):
        for X, Y in itertools.permutations(sb.COLS, 2):
            for odd in range(3):
                targets = [set(Y) if t == odd else set(X) for t in range(3)]
                self.assertIsNotNone(sb.label_for(targets))
        self.assertIsNone(sb.label_for([{0, 1}, {0, 1}, {0, 1}]))
        self.assertIsNone(sb.label_for([{0, 1}, {0, 2}, {1, 2}]))

    def test_lift_twice(self):
        maps, col = sb.family_K4(), sb.colouring_K4()
        size = 30
        for n in (4, 5):
            maps, col = sb.lift(maps, n, col)
            self.assertTrue(sb.is_full_family(maps, n + 1))
            K = kakeya_set(maps, n + 1)
            self.assertEqual(len(K), 2 * size + 1)
            self.assertTrue(is_kakeya(K, n + 1))
            self.assertTrue(sb.is_good_colouring(maps, n + 1, col))
            size = len(K)
        self.assertEqual(size, 123)

    def test_lifted_sizes_formula(self):
        sizes = sb.lifted_sizes(7)
        for n, s in sizes.items():
            self.assertEqual(s, 31 * 2 ** (n - 4) - 1)
            self.assertLess(s, 2 ** (n + 1) - 1)


class TestResultsFile(unittest.TestCase):
    @unittest.skipUnless(os.path.exists(RESULTS), "results file not present")
    def test_matches_code(self):
        with open(RESULTS) as fh:
            stored = json.load(fh)
        self.assertEqual(stored, json.loads(json.dumps(sb.results())))


if __name__ == "__main__":
    unittest.main()
