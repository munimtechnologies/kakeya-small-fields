# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest
from fractions import Fraction

from cubeloss import (SMALL, Table, agl1, construction_gpk, d_max, entropy_sides, exhaustive,
                      gpk, l_r, random_joint)


class Groups(unittest.TestCase):
    def test_orders_and_derived(self):
        expect = {"S3": (6, 3), "Z4xZ2": (8, 1), "D4": (8, 2), "Q8": (8, 2), "A4": (12, 4),
                  "D6": (12, 3)}
        for name, (n, g) in expect.items():
            G = Table(SMALL[name])
            self.assertEqual((G.n, G.derived_order()), (n, g), name)

    def test_gpk_and_agl(self):
        self.assertEqual(Table(gpk(3, 1)).derived_order(), 3)
        self.assertEqual(Table(gpk(2, 2)).derived_order(), 4)
        G = Table(agl1(7))
        self.assertEqual((G.n, G.derived_order()), (42, 7))


class Theorem25(unittest.TestCase):
    def test_every_K_small_groups(self):
        for name in ("S3", "Z4xZ2", "D4", "Q8"):
            g, worst, worst_abelian = exhaustive(Table(SMALL[name]))
            self.assertGreaterEqual(worst[0], 1, name)
            if g == 1:
                self.assertGreaterEqual(worst_abelian[0], 1, name)

    def test_entropy_inequality(self):
        rng = random.Random(7)
        for name in ("S3", "D4", "Q8"):
            G = Table(SMALL[name])
            for _ in range(400):
                S, Hd, Hd2, I, Hzc = entropy_sides(G, random_joint(G, rng, rng.randint(1, 30)))
                self.assertGreaterEqual(S, Hd + max(Hd2, I) - 1e-9)
                self.assertGreaterEqual(Hd + max(Hd2, I), 1.5 * Hd - 0.5 * Hzc - 1e-9)

    def test_gpk_construction_is_sharp_up_to_2(self):
        # |K| = 2 p^k, |D| = (p - 1) p^(3k), |G'| = p^k: |K|^8 |G'| / |D|^3 = 2^8 / (p - 1)^3.
        for p, k in [(2, 1), (2, 2), (3, 1)]:
            G, K, D, Dm = construction_gpk(p, k, (0, 1))
            g = G.derived_order()
            self.assertEqual((len(K), len(D), g), (2 * p ** k, (p - 1) * p ** (3 * k), p ** k))
            self.assertTrue(D <= Dm)
            self.assertEqual(Fraction(len(K) ** 8 * g, len(D) ** 3), Fraction(256, (p - 1) ** 3))
            self.assertGreaterEqual(Fraction(len(K) ** 8 * g, len(Dm) ** 3), 1)

    def test_exponent_one_eighth_is_needed(self):
        # In G(2, k) any bound |K|^8 |G'|^a >= c |D|^3 with a < 1 fails for large k: the family has
        # |K|^8 |G'|^a / |D|^3 = 2^8 2^((a - 1) k) -> 0.
        for k in range(1, 40):
            self.assertEqual(Fraction((2 * 2 ** k) ** 8 * 2 ** k, ((2 ** (3 * k))) ** 3), 256)
        self.assertLess(Fraction((2 * 2 ** 40) ** 16 * 2 ** 40, (2 ** 120) ** 6), Fraction(1, 2 ** 20))

    def test_agl_served_and_bound(self):
        G = Table(agl1(5))
        K = [G.idx[(a, b)] for a in range(1, 5) for b in (0, 1)]
        Dm = d_max(G, K)
        self.assertTrue({(g, h) for g in range(G.n) for h in range(G.n)
                         if G.el[h][1] == 0} <= Dm)
        self.assertGreaterEqual(Fraction(len(K) ** 8 * 5, len(Dm) ** 3), 1)

    def test_l_r(self):
        self.assertEqual([l_r(r) for r in (1, 2, 3, 4)],
                         [0, Fraction(1, 2), Fraction(13, 6), Fraction(77, 12)])


if __name__ == "__main__":
    unittest.main()
