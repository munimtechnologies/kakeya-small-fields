# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import math
import random
import unittest

from prop31_cubes import groups, inverses, perm_group
from twosided import (agl_design, class_losses, commutator_subgroup, conj, cube_points, design_law,
                      free_class2_exp3, gpk, gpk_stabiliser, max_class, random_law, schemes)


class TestClassSizes(unittest.TestCase):
    def test_derived_and_b(self):
        named = dict(groups())
        named["S_4"] = perm_group([(1, 0, 2, 3), (1, 2, 3, 0)])
        expected = {"S_3": (3, 3), "D_4": (2, 2), "Q_8": (2, 2), "A_4": (4, 4), "AGL(1,5)": (5, 5),
                    "S_4": (12, 8)}
        for name, (derived, b) in expected.items():
            T = named[name]
            self.assertEqual(len(commutator_subgroup(T)), derived, name)
            self.assertEqual(max_class(T), b, name)

    def test_free_class2(self):
        T = free_class2_exp3()
        self.assertEqual(len(T), 729)
        self.assertEqual(len(commutator_subgroup(T)), 27)
        self.assertEqual(max_class(T), 9)

    def test_gpk_b_equals_derived(self):
        for p, k in ((2, 1), (2, 2), (3, 1)):
            _, T = gpk(p, k)
            self.assertEqual(len(commutator_subgroup(T)), p ** k)
            self.assertEqual(max_class(T), p ** k)


class TestTwoSided(unittest.TestCase):
    def test_identity(self):
        T = perm_group([(1, 0, 2, 3), (1, 2, 3, 0)])
        inv, rng = inverses(T), random.Random(0)
        for _ in range(300):
            o = tuple(rng.randrange(24) for _ in range(4))
            w = [conj(T, inv, o[0], x) for x in o[1:]]
            right = cube_points(T, (0,) + tuple(w))
            self.assertEqual(cube_points(T, o), [T[y][o[0]] for y in right])

    def test_outside_in_random(self):
        rng = random.Random(2)
        for name in ("S_3", "Q_8"):
            T = groups()[name]
            for trial in range(200):
                law = random_law(len(T), 2 + trial % 2, rng, rng.choice((3, 8, 20)))
                lhs, sides, _ = schemes(T, law)
                for key, v in sides.items():
                    self.assertGreaterEqual(lhs, v - 1e-9, (name, key))

    def test_abelian_d1_first_holds(self):
        T = perm_group([tuple((x + 1) % 8 for x in range(8))])
        rng = random.Random(3)
        for trial in range(200):
            lhs, _, wrong = schemes(T, random_law(8, 2 + trial % 2, rng, 10))
            self.assertGreaterEqual(lhs, wrong - 1e-9)

    def test_class_losses(self):
        T = perm_group([(1, 0, 2, 3), (1, 2, 3, 0)])
        rng = random.Random(4)
        for _ in range(200):
            hc, hw = class_losses(T, random_law(24, 2, rng, 15))
            self.assertLessEqual(hc, math.log2(8) + 1e-9)
            self.assertLessEqual(hw, math.log2(8) + 1e-9)

    def test_agl17_control(self):
        T, K, D = agl_design(17, 3, 2)
        self.assertEqual((len(T), len(K), len(D)), (272, 32, 4352))
        lhs, sides, wrong = schemes(T, design_law(T, K, D))
        self.assertLessEqual(lhs, 4 * math.log2(32) + 1e-9)
        self.assertGreater(wrong, 4 * math.log2(32))                # the d_1-first side fails
        for v in sides.values():
            self.assertGreaterEqual(lhs, v - 1e-9)

    def test_agl5_r3_design(self):
        T, K, D = agl_design(5, 2, 3)
        self.assertEqual(len(D), 320)
        lhs, sides, _ = schemes(T, design_law(T, K, D))
        for v in sides.values():
            self.assertGreaterEqual(lhs, v - 1e-9)


class TestStabiliser(unittest.TestCase):
    def test_gpk_core_free(self):
        for p, k, S in ((2, 1, (0, 1)), (2, 2, (0, 1)), (3, 1, (0, 1)), (5, 1, (0, 1, 2))):
            self.assertEqual(gpk_stabiliser(p, k, S), (p ** k, True, 1))


if __name__ == "__main__":
    unittest.main()
