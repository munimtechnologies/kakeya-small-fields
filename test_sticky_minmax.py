# Tests for sticky_minmax.py (note a184). Stdlib only.
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
# Every assertion is a hand computation from note a184 or a direct consequence of a proved
# statement there (Lemma 154, Propositions 79-81).

import itertools
import json
import os
import random
import unittest
from fractions import Fraction

import sticky_minmax as sm


class TestOps(unittest.TestCase):
    def test_leaf_steps(self):
        leaf3 = (sm.LEAF,) * 3
        self.assertEqual(sm.triangle(leaf3), (2, 2, 2))
        self.assertEqual(sm.affine(leaf3, 0), (1, 3, 3))

    def test_iso_permutations_covered_by_reordering(self):
        rows = [(1, 3, 3), (2, 2, 2), (3, 1, 3)]
        for iso in itertools.permutations(range(3)):
            reordered = [rows[iso[t]] for t in range(3)]
            self.assertEqual(sm.triangle(rows, iso), sm.triangle(reordered))


class TestLemma154Doubling(unittest.TestCase):
    def test_triangle_of_equal_children_doubles(self):
        rng = random.Random(154)
        for _ in range(300):
            v = tuple(rng.randint(1, 50) for _ in range(3))
            self.assertEqual(sm.triangle([v, v, v]), tuple(2 * x for x in v))


class TestProposition79Cyclic(unittest.TestCase):
    def test_cyclic_children_are_relabellings(self):
        rng = random.Random(79)
        for _ in range(300):
            v = tuple(rng.randint(1, 60) for _ in range(3))
            for c in sm.cyclic_children(v):
                self.assertEqual(sorted(c), sorted(v))

    def test_cyclic_triangle_gives_min_plus_max(self):
        rng = random.Random(791)
        vecs = [tuple(rng.randint(1, 60) for _ in range(3)) for _ in range(300)]
        vecs += [(1, 3, 3), (2, 2, 2), (3, 3, 9), (3, 4, 8), (1, 9, 9)]
        for v in vecs:
            k = sm.min_plus_max(v)
            self.assertEqual(sm.triangle(sm.cyclic_children(v)), (k, k, k))

    def test_next_height_reaches_min_plus_max(self):
        fr = sm.fronts(2)
        for h in (1, 2):
            k = min(sm.min_plus_max(v) for v in fr[h])
            nxt = sm.next_front(fr[h], U=k)
            self.assertTrue(any(sm.leq(w, (k, k, k)) for w in nxt))


class TestProposition80Fronts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.fr = sm.fronts(2)

    def test_front_h1(self):
        self.assertEqual(self.fr[1], [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])

    def test_front_h2_is_the_hand_list(self):
        self.assertEqual(self.fr[2], sm.hand_front_h2())
        self.assertEqual(len(self.fr[2]), 19)

    def test_357_is_dominated(self):
        self.assertNotIn((3, 5, 7), self.fr[2])
        self.assertTrue(sm.leq((3, 5, 5), (3, 5, 7)))

    def test_f_values(self):
        self.assertEqual(min(max(v) for v in self.fr[1]), 2)
        self.assertEqual(min(max(v) for v in self.fr[2]), 4)

    def test_f3_is_8(self):
        self.assertEqual(sm.next_front(self.fr[2], U=7), [])
        f3 = sm.next_front(self.fr[2], U=8)
        self.assertTrue(any(sm.leq(w, (8, 8, 8)) for w in f3))
        self.assertEqual(sm.triangle([(4, 4, 4)] * 3), (8, 8, 8))
        self.assertEqual(min(max(v) for v in f3), 8)

    def test_hand_proof_ingredients(self):
        # affine root: every height-2 vector has each pair of coordinates summing to >= 6
        self.assertEqual(min(v[a] + v[b] for v in self.fr[2] for a, b in ((0, 1), (0, 2), (1, 2))), 6)

    def test_conjecture_M_at_heights_1_and_2(self):
        self.assertEqual(min(sm.min_plus_max(v) for v in self.fr[1]), 4)
        self.assertEqual(min(sm.min_plus_max(v) for v in self.fr[2]), 8)
        line = [v for v in self.fr[2] if sm.min_plus_max(v) == 8 and v[0] <= v[1] == v[2]]
        self.assertEqual(line, [(2, 6, 6), (3, 5, 5), (4, 4, 4)])


class TestProposition81(unittest.TestCase):
    def test_affine_chain(self):
        v = sm.LEAF
        for h in range(1, 7):
            v = sm.affine([v] * 3, 0)
            self.assertEqual(v, (1, 3 ** h, 3 ** h))

    def test_zero_chain_shrinks_above_sqrt3(self):
        # beta = 7/4: beta^2 = 49/16 > 3, so each double step multiplies by 48/49
        seq = sm.zero_chain((0, 5, 7), 7, 4, 6)
        for k, v in enumerate(seq):
            r = Fraction(48, 49) ** k
            self.assertEqual(v, (Fraction(0), 5 * r, 7 * r))

    def test_zero_chain_grows_below_sqrt3(self):
        # beta = 17/10: beta^2 = 289/100 < 3
        seq = sm.zero_chain((0, 1, 1), 17, 10, 4)
        for k, v in enumerate(seq):
            r = Fraction(300, 289) ** k
            self.assertEqual(v, (Fraction(0), r, r))

    def test_threshold(self):
        self.assertLess(Fraction(17, 10) ** 2, 3)
        self.assertGreater(Fraction(7, 4) ** 2, 3)


class TestResultsFile(unittest.TestCase):
    PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "results", "sticky_minmax.json")

    @unittest.skipUnless(os.path.exists(PATH), "results file not present next to the tests")
    def test_matches_code(self):
        with open(self.PATH) as fh:
            stored = json.load(fh)
        fresh = json.loads(json.dumps(sm.results()))
        for key in ("front_sizes", "front_h1", "front_h2_shapes", "f",
                    "height3_vectors_with_max_at_most_7", "min_plus_max", "minplusmax_line_h2"):
            self.assertEqual(stored[key], fresh[key], msg=key)
        self.assertAlmostEqual(stored["sqrt3_threshold"], fresh["sqrt3_threshold"], delta=1e-12)


if __name__ == "__main__":
    unittest.main()
