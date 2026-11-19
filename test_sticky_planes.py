# test_sticky_planes.py -- checks for note a186 (sticky_planes.py).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only.

import itertools
import json
import os
import random
import unittest

import sticky_planes as sp

SHAPES_H2 = [(4, 4, 4), (3, 5, 5), (2, 6, 6), (1, 9, 9), (3, 3, 9), (3, 4, 8)]


def perms(v):
    return set(tuple(v[p[t]] for t in range(3)) for p in itertools.permutations(range(3)))


class TestGame(unittest.TestCase):

    def test_front_h2_is_a184_list(self):
        fr = sp.fronts(2)
        self.assertEqual(sorted(fr[1]), [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])
        want = set()
        for s in SHAPES_H2:
            want |= perms(s)
        self.assertEqual(set(fr[2]), want)
        self.assertEqual(len(fr[2]), 19)

    def test_plane_bound_closed_form(self):
        rng = random.Random(1)
        for _ in range(2000):
            a = tuple(rng.randint(1, 40) for _ in range(3))
            U = rng.randint(0, 60)
            self.assertEqual(sp.plane_bound(a, U), sum(a) + max(0, U - max(a)))

    def test_plane_bound_monotone(self):
        rng = random.Random(2)
        for _ in range(2000):
            a = [rng.randint(1, 30) for _ in range(3)]
            b = list(a)
            b[rng.randrange(3)] += rng.randint(0, 5)
            U = rng.randint(0, 40)
            self.assertLessEqual(sp.plane_bound(tuple(a), U), sp.plane_bound(tuple(b), U))
            self.assertLessEqual(sp.plane_bound(tuple(a), U), sp.plane_bound(tuple(a), U + 1))

    def test_G_values(self):
        self.assertEqual(sp.g_bounds(4), [0, 3, 7, 15, 29])

    def test_witnesses(self):
        fr2 = set(sp.fronts(2)[2])
        for name, kids in sp.WITNESS_CHILDREN.items():
            for v in kids:
                self.assertIn(tuple(v), fr2)
        w = sp.witness_vectors()
        self.assertEqual(w["triangle_8_6_14"], [8, 6, 14])
        self.assertEqual(w["triangle_7_7_13"], [7, 7, 13])
        self.assertEqual(w["affine0_5_9_15"], [5, 9, 15])
        for v in w.values():
            self.assertEqual(sp.plane_bound(tuple(v), 15), 29)

    def test_general_rule_matches_node_rules(self):
        self.assertEqual(sp.game_vector({(): (0, 0, 0)}, 1), (1, 3, 3))
        self.assertEqual(sp.game_vector({(): (0, 2, 1)}, 1), (3, 1, 3))   # g(x) = -x
        self.assertEqual(sp.game_vector({(): (0, 1, 1)}, 1), (2, 2, 2))   # g(x) = x^2


class TestRealSets(unittest.TestCase):

    def test_classical(self):
        for n in range(1, 5):
            K = sp.kakeya_set(sp.classical_maps(n), n)
            self.assertEqual(len(K), 2 ** (n + 1) - 1)
            want = set(itertools.product((0, 1), repeat=n)) | set(itertools.product((0, 2), repeat=n))
            self.assertEqual(K, want)
            if n <= 3:
                self.assertTrue(sp.is_kakeya(K, n))

    def test_real_slices_dominate_game(self):
        rng = random.Random(3)
        for k in (1, 2, 3):
            for _ in range(150):
                maps = sp.random_maps(k, rng)
                S = sp.slices(maps, k)
                L = sp.game_vector(maps, k)
                for t in range(3):
                    self.assertGreaterEqual(len(S[t]), L[t])

    def test_slice_union_contains_kakeya(self):
        rng = random.Random(4)
        for k in (1, 2, 3):
            for _ in range(50):
                maps = sp.random_maps(k, rng)
                S = sp.slices(maps, k)
                self.assertTrue(sp.kakeya_set(maps, k) <= (S[0] | S[1] | S[2]))

    def test_decomposition_identity(self):
        rng = random.Random(5)
        for n in (1, 2, 3, 4):
            reps = 300 if n <= 3 else 60
            for _ in range(reps):
                maps = sp.random_maps(n, rng)
                self.assertEqual(len(sp.kakeya_set(maps, n)), sp.decomposition_size(maps, n))
        for n in (2, 3):
            maps = sp.classical_maps(n)
            self.assertEqual(sp.decomposition_size(maps, n), 2 ** (n + 1) - 1)

    def test_construction(self):
        rng = random.Random(6)
        for m in (1, 2, 3):
            reps = 200 if m <= 2 else 40
            for _ in range(reps):
                mK = sp.random_maps(m, rng)
                mT = sp.random_maps(m, rng)
                h = rng.randrange(3)
                w = tuple(rng.randrange(3) for _ in range(m))
                maps = sp.construct(mK, mT, h, w, m)
                # sticky by construction: one map per prefix of length < m + 1
                want_keys = set()
                for j in range(m + 1):
                    want_keys |= set(itertools.product(range(3), repeat=j))
                self.assertEqual(set(maps), want_keys)
                K = sp.kakeya_set(maps, m + 1)
                self.assertEqual(len(K), sp.formula_size(mK, mT, h, w, m))
                if m <= 2 and rng.random() < 0.1:
                    self.assertTrue(sp.is_kakeya(K, m + 1))

    def test_dim2_row(self):
        for r0 in range(3):
            for g0 in itertools.product(range(3), repeat=3):
                pts = set()
                for y in (1, 2):
                    for t in range(3):
                        pts.add((r0, (g0[y] + t * y) % 3))
                self.assertEqual(pts, {(r0, v) for v in range(3)})

    def test_exhaustive_dim2(self):
        self.assertEqual(sp.min_sticky_dim2(), 7)

    def test_random_configs_respect_bounds(self):
        rng = random.Random(7)
        G = [0, 3, 7, 15, 29]
        for n in (1, 2, 3, 4):
            for _ in range(200 if n <= 3 else 80):
                maps = sp.random_maps(n, rng)
                self.assertGreaterEqual(len(sp.kakeya_set(maps, n)), G[n])


class TestResultsFile(unittest.TestCase):
    PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "sticky_planes.json")

    @unittest.skipUnless(os.path.exists(PATH), "results file not present next to the tests")
    def test_matches(self):
        with open(self.PATH) as fh:
            saved = json.load(fh)
        fresh = json.loads(json.dumps(sp.results()))
        self.assertEqual(saved, fresh)


if __name__ == "__main__":
    unittest.main()
