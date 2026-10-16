# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import math
import random
import unittest
from fractions import Fraction

from orderlp import (MIX3, coverage, cube_sum, entropy, gpk_lower, l_r, lam, loss, main_term,
                     order_slacks, problem, random_law, simplex, small_groups, theorem_slack,
                     vertex_min)


class Orders(unittest.TestCase):
    def test_loss_tables(self):
        self.assertEqual({s: loss(s) for s in itertools.permutations((1, 2))}, {(1, 2): 1, (2, 1): 0})
        self.assertEqual({s: loss(s) for s in itertools.permutations((1, 2, 3))},
                         {(3, 2, 1): 0, (3, 1, 2): 1, (2, 3, 1): 2, (2, 1, 3): 3, (1, 3, 2): 3,
                          (1, 2, 3): 4})

    def test_uniform_average_is_l_r(self):
        self.assertEqual([l_r(r) for r in (1, 2, 3, 4)],
                         [0, Fraction(1, 2), Fraction(13, 6), Fraction(77, 12)])
        for r in range(1, 6):
            orders = list(itertools.permutations(range(1, r + 1)))
            self.assertEqual(Fraction(sum(loss(s) for s in orders), len(orders)), l_r(r))

    def test_coverage(self):
        self.assertEqual(coverage((3, 2, 1)), [0, 1, 3])
        for s in itertools.permutations(range(1, 5)):
            self.assertEqual(sum(coverage(s)), 2 ** 4 - 1 - 4)

    def test_gpk_lower(self):
        self.assertEqual([gpk_lower(r) for r in (2, 3, 4)],
                         [Fraction(1, 8), Fraction(1, 6), Fraction(11, 64)])


class LP(unittest.TestCase):
    def test_tiny_lp(self):
        # min x + 2y subject to x + y = 1: optimum 1 at x = 1
        value, x, basis = simplex([[1, 1]], [1], [1, 2])
        self.assertEqual((value, x), (1, [1, 0]))

    def test_r2_and_r3(self):
        self.assertEqual(lam(2)[0], Fraction(1, 2))
        self.assertEqual(lam(3)[0], 2)

    def test_hand_certificate_r3(self):
        orders, A, b, c = problem(3)
        x = [MIX3.get(s, Fraction(0)) for s in orders]
        for i in range(3):
            self.assertEqual(sum(A[i][j] * x[j] for j in range(6)), Fraction(4, 3))
        self.assertEqual(sum(c[j] * x[j] for j in range(6)), 2)
        y = [Fraction(15, 14), Fraction(9, 14), Fraction(-3, 14)]
        for j in range(6):
            self.assertLessEqual(sum(A[i][j] * y[i] for i in range(3)), c[j])
        self.assertEqual(sum(b[i] * y[i] for i in range(3)), 2)

    def test_vertex_enumeration_agrees(self):
        for r in (2, 3):
            _, A, b, c = problem(r)
            self.assertEqual(vertex_min(A, b, c), lam(r)[0])

    def test_lp_never_beats_construction(self):
        for r in (2, 3, 4):
            self.assertGreaterEqual(lam(r)[0] / 2 ** r, gpk_lower(r))
            self.assertLessEqual(lam(r)[0], l_r(r))


class Entropy(unittest.TestCase):
    def test_derived_orders(self):
        self.assertEqual({G.name: G.derived_order() for G in small_groups()},
                         {"Z2xZ4": 1, "S3": 3, "D4": 2, "Q8": 2})

    def test_shearer_main_term_mix3(self):
        # sum_sigma w_sigma (2 H(d_sigma1) + H(d_sigma1, d_sigma2)) >= (4/3) H(d) on random laws
        rng = random.Random(3)
        G = small_groups()[0]
        for _ in range(200):
            law = random_law(G, 3, rng, rng.randint(1, 30))
            mix = sum(float(w) * main_term(law, s) for s, w in MIX3.items())
            self.assertGreaterEqual(mix, 7 / 3 * entropy(law, lambda o: o[1:]) - 1e-9)

    def test_per_order_lemma_and_theorem(self):
        rng = random.Random(11)
        for G in small_groups():
            for r in (2, 3):
                for _ in range(60):
                    law = random_law(G, r, rng, rng.choice((1, 3, 8, 20)))
                    self.assertGreaterEqual(order_slacks(G, law, r), -1e-9, G.name)
                    if r == 3:
                        self.assertGreaterEqual(theorem_slack(G, law), -1e-9, G.name)

    def test_uniform_law_reverse_order_is_lossless(self):
        # A = e, d uniform on Q8^2: the reverse order needs no loss term at all
        G = small_groups()[3]
        law = [((G.e, a, b), 1 / 64) for a in range(8) for b in range(8)]
        self.assertGreaterEqual(cube_sum(G, law, 2) - main_term(law, (2, 1)), -1e-9)
        self.assertAlmostEqual(cube_sum(G, law, 2), 2 * 0 + 3 * math.log2(8))


if __name__ == "__main__":
    unittest.main()
