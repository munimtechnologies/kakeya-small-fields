# Tests for sticky_pi4.py.  MV2 of Munim, Inc. Made with AI agents working in MV2's name.
# Licence: Apache-2.0.

import itertools
import random
import unittest

from sticky_pi3 import ALL_MAPS, height2_vectors, minimal, node_lower
from sticky_pi4 import is_affine, minimal_fast, quad_min


class TestPi4(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.v2 = height2_vectors()
        cls.M2 = minimal(cls.v2)

    def test_affine_count(self):
        # g(x) = a x + b: 9 affine maps, 18 quadratic ones.
        self.assertEqual(sum(1 for g in ALL_MAPS if is_affine(g)), 9)

    def test_quadratic_root_shape(self):
        # A quadratic root has a 2+1 pattern in every slice, and the lone child is a bijection of t.
        for g in ALL_MAPS:
            if is_affine(g):
                continue
            iso = []
            for t in range(3):
                vals = [(g[x] + t * x) % 3 for x in range(3)]
                self.assertEqual(len(set(vals)), 2)
                iso.append([x for x in range(3) if vals.count(vals[x]) == 1][0])
            self.assertEqual(sorted(iso), [0, 1, 2])

    def test_minimal_fast_matches(self):
        self.assertEqual(minimal_fast(self.v2), self.M2)
        rng = random.Random(7)
        for _ in range(20):
            vecs = {tuple(rng.randint(1, 9) for _ in range(3)) for _ in range(rng.randint(1, 60))}
            self.assertEqual(minimal_fast(vecs), minimal(vecs))

    def test_height2_facts(self):
        self.assertEqual(min(a * b * c for a, b, c in self.M2), 64)
        self.assertIn((4, 4, 4), self.M2)

    def test_quad_formula_matches_brute_force(self):
        brute = min(
            node_lower(g, kids)[0] * node_lower(g, kids)[1] * node_lower(g, kids)[2]
            for kids in itertools.product(self.M2, repeat=3)
            for g in ALL_MAPS if not is_affine(g))
        q, wit, _ = quad_min(self.M2)
        self.assertEqual(q, brute)
        self.assertEqual(q, 512)
        L = wit["L"]
        self.assertEqual(L[0] * L[1] * L[2], q)

    def test_quad_formula_random_sets(self):
        rng = random.Random(11)
        for _ in range(5):
            M = sorted({tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(8)})
            brute = min(
                node_lower(g, kids)[0] * node_lower(g, kids)[1] * node_lower(g, kids)[2]
                for kids in itertools.product(M, repeat=3)
                for g in ALL_MAPS if not is_affine(g))
            self.assertEqual(quad_min(M)[0], brute)

    def test_affine_lemma(self):
        # Affine roots: P^3 >= 729 G_A G_B G_C on every triple of minimal height-2 vectors.
        for kids in itertools.product(self.M2, repeat=3):
            G = 1
            for k in kids:
                G *= k[0] * k[1] * k[2]
            for g in ALL_MAPS:
                if is_affine(g):
                    L = node_lower(g, kids)
                    self.assertGreaterEqual((L[0] * L[1] * L[2]) ** 3, 729 * G)

    def test_quad_min_respects_cutoff(self):
        q, wit, _ = quad_min(self.M2, 512)
        self.assertEqual(q, 512)
        self.assertIsNone(wit)


if __name__ == "__main__":
    unittest.main()
