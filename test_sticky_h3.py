# Tests for sticky_h3.py.  MV2 of Munim, Inc. Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only; needs only sticky_h3.py.

import itertools
import random
import unittest

from sticky_h3 import (ALL_MAPS, PC, build_tables, decode, enumerate_height2, exact_quadratic,
                       group_elements, inclusion_minimal, make_inW, mask_tables, minimal3,
                       orbit_reps, quad_min, transformed_tree, tree_masks, w_tables, game_front3)

G = group_elements()
TABS = mask_tables(G)


def naive_quadratic(pool, inW):
    out = set()
    for A in pool:
        for B in pool:
            for C in pool:
                L = (PC[A[0]] + PC[B[0] | C[0]], PC[B[1]] + PC[A[1] | C[1]],
                     PC[C[2]] + PC[A[2] | B[2]])
                if inW(L):
                    out.add(L)
    return minimal3(out)


def closure(trees):
    pool = set()
    for (m0, m1, m2) in trees:
        for t in TABS:
            pool.add((t[m0], t[m1], t[m2]))
    return sorted(pool)


def pipeline(pool, inW, caps):
    trees = [(m0, m1, m2, i) for i, (m0, m1, m2) in enumerate(pool)]
    TA, TB, TC = build_tables(trees)
    TA, TB, TC = inclusion_minimal(TA), inclusion_minimal(TB), inclusion_minimal(TC)
    found, complete, _ = exact_quadratic(TA, TB, orbit_reps(TC, TABS), inW, caps)
    assert complete
    return minimal3(found.keys()), found


class TestStickyH3(unittest.TestCase):
    def test_group_size_and_bijection(self):
        self.assertEqual(len(G), 108)
        for t in TABS:
            self.assertEqual(sorted(t), list(range(512)))
            self.assertTrue(all(PC[t[m]] == PC[m] for m in range(512)))

    def test_group_maps_trees_to_trees(self):
        rng = random.Random(3)
        for _ in range(40):
            r, h0, h1, h2 = (rng.randrange(27) for _ in range(4))
            m = tree_masks(r, h0, h1, h2)
            for g, t in zip(G, TABS):
                img = tree_masks(*transformed_tree(g, r, (h0, h1, h2)))
                self.assertEqual(img, (t[m[0]], t[m[1]], t[m[2]]))

    def test_classical_tree(self):
        # P(d) = (d1^2, d2^2): slices are 2x2 grids.
        sq = ALL_MAPS.index((0, 1, 1))
        m = tree_masks(sq, sq, sq, sq)
        self.assertEqual([PC[x] for x in m], [4, 4, 4])

    def test_enumeration_matches_tree_masks_and_counts(self):
        rng = random.Random(5)
        picks = set(rng.randrange(27 ** 4) for _ in range(50))
        vecs = set()
        for m0, m1, m2, code in enumerate_height2():
            vecs.add((PC[m0], PC[m1], PC[m2]))
            if code in picks:
                self.assertEqual((m0, m1, m2), tree_masks(*decode(code)))
        self.assertEqual(len(vecs), 96)
        M2 = minimal3(vecs)
        self.assertEqual(len(M2), 19)
        self.assertIn((4, 4, 4), M2)
        self.assertIn((2, 6, 6), M2)

    def test_quadratic_root_formula_on_classical(self):
        # Height-3 classical tree: root x^2 over three classical children gives (8, 8, 8).
        sq = ALL_MAPS.index((0, 1, 1))
        C = tree_masks(sq, sq, sq, sq)
        L = (PC[C[0]] + PC[C[0] | C[0]], PC[C[1]] + PC[C[1] | C[1]], PC[C[2]] + PC[C[2] | C[2]])
        self.assertEqual(L, (8, 8, 8))

    def test_pipeline_matches_naive_box(self):
        rng = random.Random(11)
        for _ in range(2):
            trees = [tree_masks(*(rng.randrange(27) for _ in range(4)))]
            pool = closure(trees)
            box = (rng.randint(6, 14), rng.randint(6, 14), rng.randint(6, 14))
            inW = lambda L, b=box: 1 <= L[0] <= b[0] and 1 <= L[1] <= b[1] and 1 <= L[2] <= b[2]
            got, found = pipeline(pool, inW, box)
            self.assertEqual(got, naive_quadratic(pool, inW))

    def test_pipeline_matches_naive_full(self):
        rng = random.Random(17)
        trees = [tree_masks(*(rng.randrange(27) for _ in range(4)))]
        pool = closure(trees)
        inW = lambda L: True
        got, _ = pipeline(pool, inW, (99, 99, 99))
        self.assertEqual(got, naive_quadratic(pool, inW))

    def test_inclusion_minimal(self):
        T = {0b1: 5 * 10 ** 6, 0b11: 5 * 10 ** 6, 0b10: 7 * 10 ** 6, 0b111: 4 * 10 ** 6}
        out = inclusion_minimal(T)
        self.assertEqual(sorted(out), [0b1, 0b10, 0b111])

    def test_inclusion_minimal_methods_agree(self):
        rng = random.Random(31)
        T = {}
        for i in range(300):
            k = rng.randrange(1, 1 << 18) & rng.randrange(1, 1 << 18) & rng.randrange(1, 1 << 18)
            if k:
                T[k] = rng.randint(1, 9) * 10 ** 6 + i
        self.assertEqual(inclusion_minimal(T, "pairs"), inclusion_minimal(T, "sos"))

    def test_w_tables_brute(self):
        rng = random.Random(23)
        F = [tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(6)]
        vmax = w_tables(F)
        inW, _ = make_inW(vmax)

        def tri(A, B, C):
            return ((A[0] + max(B[0], C[0])) * (B[1] + max(A[1], C[1]))
                    * (C[2] + max(A[2], B[2])))

        for _ in range(400):
            v = tuple(rng.randint(1, 27) for _ in range(3))
            brute = any(tri(v, X, Y) < 4096 or tri(X, v, Y) < 4096 or tri(X, Y, v) < 4096
                        for X in F for Y in F)
            self.assertEqual(inW(v), brute, v)

    def test_game_front3_known(self):
        M2 = [(1, 9, 9), (2, 6, 6), (3, 3, 9), (3, 4, 8), (3, 5, 5), (3, 8, 4), (3, 9, 3),
              (4, 3, 8), (4, 4, 4), (4, 8, 3), (5, 3, 5), (5, 5, 3), (6, 2, 6), (6, 6, 2),
              (8, 3, 4), (8, 4, 3), (9, 1, 9), (9, 3, 3), (9, 9, 1)]
        F3 = game_front3(M2)
        self.assertEqual(len(F3), 112)
        self.assertIn((7, 7, 12), F3)
        self.assertEqual(min(a * b * c for a, b, c in F3), 512)

    def test_quad_min_brute(self):
        rng = random.Random(29)
        for _ in range(5):
            M = sorted({tuple(rng.randint(1, 12) for _ in range(3)) for _ in range(8)})
            brute = min((A[0] + max(B[0], C[0])) * (B[1] + max(A[1], C[1]))
                        * (C[2] + max(A[2], B[2])) for A, B, C in itertools.product(M, repeat=3))
            self.assertEqual(quad_min(M)[0], brute)


if __name__ == "__main__":
    unittest.main()
