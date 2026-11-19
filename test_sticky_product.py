# Tests for sticky_product.py (note a188). MV2 of Munim, Inc. Made with AI agents. Apache-2.0.
import itertools
import json
import os
import random
import unittest

from sticky_planes import (slices, kakeya_set, random_maps, classical_maps, sub, construct,
                           formula_size)
from sticky_break import tree_T, family_K3, family_K4, MAPS_Y, MAPS_X, MAPS_Z, is_full_family
import sticky_product as sp

HERE = os.path.dirname(os.path.abspath(__file__))
RESULTS = os.path.join(HERE, "results", "sticky_product.json")


def shift_set(S, w):
    return {tuple((p[j] + w[j]) % 3 for j in range(len(w))) for p in S}


class TestLemma161(unittest.TestCase):
    def test_rotate_and_reflect(self):
        rng = random.Random(161)
        for k in (1, 2, 3):
            for _ in range(5):
                m = random_maps(k, rng)
                S = slices(m, k)
                for c in range(3):
                    R = sp.rotate(m, c)
                    self.assertTrue(is_full_family(R, k))
                    self.assertEqual(slices(R, k), [S[(t + c) % 3] for t in range(3)])
                F = sp.reflect(m)
                self.assertTrue(is_full_family(F, k))
                self.assertEqual(slices(F, k), [S[(-t) % 3] for t in range(3)])

    def test_product_is_cartesian(self):
        rng = random.Random(1611)
        pairs = [(MAPS_Y, 2, MAPS_Z, 2), (tree_T(), 3, MAPS_X, 2)]
        for _ in range(3):
            pairs.append((random_maps(2, rng), 2, random_maps(1, rng), 1))
        for A, ka, B, kb in pairs:
            M = sp.product(A, ka, B, kb)
            self.assertTrue(is_full_family(M, ka + kb))
            SA, SB, SM = slices(A, ka), slices(B, kb), slices(M, ka + kb)
            for t in range(3):
                self.assertEqual(SM[t], {a + b for a in SA[t] for b in SB[t]})

    def test_balanced(self):
        T = tree_T()
        self.assertEqual(sp.slice_sizes(T, 3), [7, 7, 13])
        B = sp.balanced(T, 3)
        self.assertTrue(is_full_family(B, 9))
        self.assertEqual(sp.slice_sizes(B, 9), [637, 637, 637])
        C = sp.balanced(classical_maps(2), 2)
        self.assertEqual(sp.slice_sizes(C, 6), [64, 64, 64])


class TestLemma162(unittest.TestCase):
    def test_node_bound_on_random_trees(self):
        rng = random.Random(162)
        for k in (1, 2, 3):
            for _ in range(40):
                self.assertTrue(sp.node_bound_holds(random_maps(k, rng), k))

    def test_node_bound_on_known_trees(self):
        self.assertTrue(sp.node_bound_holds(tree_T(), 3))
        self.assertTrue(sp.node_bound_holds(classical_maps(4), 4))
        for m in (MAPS_Y, MAPS_X, MAPS_Z):
            self.assertTrue(sp.node_bound_holds(m, 2))

    def test_affine_detection(self):
        affine = [g for g in sp.ALL_MAPS if sp.is_affine_map(g)]
        self.assertEqual(len(affine), 9)
        for g in sp.ALL_MAPS:
            sizes = sorted(len({(g[z] + t * z) % 3 for z in range(3)}) for t in range(3))
            self.assertEqual(sizes, [1, 3, 3] if sp.is_affine_map(g) else [2, 2, 2])


class TestTheorem78Pieces(unittest.TestCase):
    def test_kakeya_set_at_least_slice_sum_of_each_subtree(self):
        rng = random.Random(78)
        fams = [(family_K4(), 4), (family_K3(), 3), (classical_maps(4), 4)]
        for n in (2, 3, 4):
            for _ in range(6):
                fams.append((random_maps(n, rng), n))
        for maps, n in fams:
            K = kakeya_set(maps, n)
            for x in (1, 2):
                self.assertGreaterEqual(len(K), sum(sp.slice_sizes(sub(maps, x), n - 1)))

    def test_construction_upper_bound(self):
        rng = random.Random(780)
        for _ in range(8):
            Kp = random_maps(2, rng)
            T = random_maps(2, rng)
            h = rng.randrange(3)
            w = (rng.randrange(3), rng.randrange(3))
            built = construct(Kp, T, h, w, 2)
            self.assertTrue(is_full_family(built, 3))
            size = len(kakeya_set(built, 3))
            self.assertEqual(size, formula_size(Kp, T, h, w, 2))
            self.assertLessEqual(size, len(kakeya_set(Kp, 2)) + sum(sp.slice_sizes(T, 2)))

    def test_slices_cover_translation(self):
        # A translated tree (constant w added at every level) has translated slices.
        T = tree_T()
        w = (1, 2, 0)
        Tw = {a: tuple((g[y] + w[len(a)]) % 3 for y in range(3)) for a, g in T.items()}
        S, Sw = slices(T, 3), slices(Tw, 3)
        for t in range(3):
            self.assertEqual(Sw[t], shift_set(S[t], w))


class TestProposition83(unittest.TestCase):
    def test_height1(self):
        self.assertEqual(sp.exhaustive_height1(), (8, 6))

    def test_height2(self):
        self.assertEqual(sp.exhaustive_height2(), (64, 12))

    def test_classical_meets_the_minimum(self):
        for k in (1, 2, 3, 4):
            self.assertEqual(sp.slice_product(classical_maps(k), k), 8 ** k)


class TestResultsFile(unittest.TestCase):
    @unittest.skipUnless(os.path.exists(RESULTS), "results file not present")
    def test_matches_code(self):
        with open(RESULTS) as fh:
            stored = json.load(fh)
        self.assertEqual(stored, json.loads(json.dumps(sp.results())))


if __name__ == "__main__":
    unittest.main()
