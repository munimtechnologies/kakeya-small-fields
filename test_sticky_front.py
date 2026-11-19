# Tests for sticky_front.py (notes/prereg-sticky-front.md). Stdlib only.
# MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
# Every assertion is either a hand computation or a proved statement (Lemmas 149-151).

import itertools
import random
import unittest

import sticky_front as sf


class TestOps(unittest.TestCase):
    def test_leaf_steps(self):
        leaf3 = (sf.LEAF,) * 3
        self.assertEqual(sf.triangle(leaf3), (2, 2, 2))
        self.assertEqual(sf.affine(leaf3, 0), (1, 3, 3))
        self.assertEqual(sf.affine(leaf3, 1), (3, 1, 3))
        self.assertEqual(sf.affine(leaf3, 2), (3, 3, 1))

    def test_hand_examples(self):
        # affine (constant slice 0) over three copies of (3,1,3) gives (3,3,9)
        self.assertEqual(sf.affine([(3, 1, 3)] * 3, 0), (3, 3, 9))
        # Latin triangle over (1,3,3),(3,1,3),(3,3,1): each slice isolates the 1 -> 1 + 3
        self.assertEqual(sf.triangle([(1, 3, 3), (3, 1, 3), (3, 3, 1)]), (4, 4, 4))
        # rows (1,3,3),(2,2,2),(2,2,2): p0 = 1+2, p1 = 2+max(3,2), p2 = 2+max(3,2)
        self.assertEqual(sf.triangle([(1, 3, 3), (2, 2, 2), (2, 2, 2)]), (3, 5, 5))
        # a non-identity bijection: slice 0 isolates child 2, slice 1 child 0, slice 2 child 1
        self.assertEqual(sf.triangle([(1, 3, 3), (2, 2, 2), (2, 2, 2)], iso=(2, 0, 1)),
                         (2 + 2, 3 + 2, 2 + 3))

    def test_iso_permutations_covered_by_reordering(self):
        rows = [(1, 3, 3), (2, 2, 2), (3, 1, 3)]
        for iso in itertools.permutations(range(3)):
            # put child iso[t] in position t, then use the identity bijection
            reordered = [rows[iso[t]] for t in range(3)]
            self.assertEqual(sf.triangle(rows, iso), sf.triangle(reordered))


class TestPareto(unittest.TestCase):
    def test_fast_equals_simple(self):
        rng = random.Random(149)
        for _ in range(40):
            vecs = [tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(rng.randint(1, 60))]
            self.assertEqual(sf.pareto_min_fast(vecs), sf.pareto_min(vecs))

    def test_small_case(self):
        self.assertEqual(sf.pareto_min_fast([(2, 2, 2), (1, 3, 3), (2, 3, 3), (2, 2, 2)]),
                         [(1, 3, 3), (2, 2, 2)])


class TestFronts(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.f1 = sf.next_front_py([sf.LEAF])
        cls.f2 = sf.next_front_py(cls.f1)
        cls.f3 = sf.next_front_py(cls.f2, U=64)

    def test_front_height_1(self):
        self.assertEqual(self.f1, [(1, 3, 3), (2, 2, 2), (3, 1, 3), (3, 3, 1)])

    def test_lemma151_f2_is_4(self):
        self.assertEqual(min(max(v) for v in self.f2), 4)

    def test_339_is_minimal_at_height_2(self):
        for v in [(3, 3, 9), (3, 9, 3), (9, 3, 3)]:
            self.assertIn(v, self.f2)

    def test_front_symmetric(self):
        for fr in (self.f1, self.f2, self.f3):
            s = set(fr)
            for v in fr:
                for perm in itertools.permutations(range(3)):
                    self.assertIn(tuple(v[perm[t]] for t in range(3)), s)

    def test_lemma150_pair_products(self):
        for h, fr in ((1, self.f1), (2, self.f2), (3, self.f3)):
            for v in fr:
                for a, b in ((0, 1), (0, 2), (1, 2)):
                    self.assertGreaterEqual(v[a] * v[b], 3 ** h)

    def test_entropy_product_bound(self):
        for h, fr in ((1, self.f1), (2, self.f2), (3, self.f3)):
            for v in fr:
                self.assertGreaterEqual(4 ** h * v[0] * v[1] * v[2], 27 ** h)

    def test_f_at_most_two_pow_h(self):
        # triangles everywhere give (8, 8, 8), so the front has a vector with max <= 8
        self.assertLessEqual(min(max(v) for v in self.f3), 8)

    def test_monotone_coordinates(self):
        # every parent coordinate is >= the same coordinate of every child
        for c in itertools.product(self.f1, repeat=3):
            for p in (sf.triangle(c), sf.affine(c, 0), sf.affine(c, 1), sf.affine(c, 2)):
                for x in c:
                    self.assertTrue(sf.leq(x, p))


if __name__ == "__main__":
    unittest.main()
