# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import unittest

import heisenberg_cubes as hc


class TestHeisenbergCubes(unittest.TestCase):
    def test_group_axioms_and_class_two(self):
        for p, k in ((2, 1), (2, 2), (3, 1)):
            G = hc.group(p, k)
            self.assertEqual(len(G), p ** (2 * k + 1))
            e = hc.identity(k)
            Z = {(0, (0,) * k, z) for z in hc.vectors(p, k)}
            for x in G:
                self.assertEqual(hc.mul(p, x, hc.inv(p, x)), e)
                self.assertEqual(hc.mul(p, e, x), x)
            for x, y, z in itertools.product(G, repeat=3):
                self.assertEqual(hc.mul(p, hc.mul(p, x, y), z), hc.mul(p, x, hc.mul(p, y, z)))
            centre = {x for x in G if all(hc.mul(p, x, y) == hc.mul(p, y, x) for y in G)}
            self.assertEqual(centre, Z)
            commutators = {hc.mul(p, hc.mul(p, hc.inv(p, x), hc.inv(p, y)), hc.mul(p, x, y))
                           for x in G for y in G}
            self.assertEqual(commutators, Z)  # G' = Z(G), so class exactly 2
        # p = 2, k = 1 is the dihedral group of order 8: five involutions
        G = hc.group(2, 1)
        self.assertEqual(sum(1 for x in G if x != hc.identity(1) and hc.mul(2, x, x) == hc.identity(1)), 5)

    def test_difference_covers(self):
        self.assertEqual([len(hc.difference_cover(p)) for p in (2, 3, 5, 7, 11, 13)], [2, 2, 3, 3, 4, 4])

    def test_brute_cover(self):
        for p, k, r in ((2, 1, 2), (2, 2, 2), (2, 2, 3), (3, 1, 2), (3, 2, 2), (5, 1, 2)):
            self.assertTrue(hc.brute_cover(p, k, r, hc.difference_cover(p)), (p, k, r))

    def test_reduction(self):
        for p, k in ((2, 2), (3, 3), (5, 2), (7, 2)):
            self.assertTrue(hc.reduction_holds(p, k, hc.difference_cover(p)), (p, k))

    def test_reduction_implies_cover_where_both_run(self):
        for p, k in ((2, 1), (2, 2), (3, 1)):
            S = hc.difference_cover(p)
            self.assertEqual(hc.reduction_holds(p, k, S), hc.brute_cover(p, k, 2, S))

    def test_abelian_bound_fails(self):
        # r = 2: |S|^8 < (p - 1)^3 p^k
        self.assertEqual(hc.least_k(2, 2, 2), 9)   # 2^8 < 2^k
        self.assertEqual(hc.least_k(3, 2, 2), 4)   # 256 < 8 * 81 = 648, but not 8 * 27 = 216
        self.assertEqual(hc.least_k(5, 2, 3), 3)   # 6561 < 64 * 125 = 8000, but not 64 * 25
        self.assertEqual(hc.least_k(7, 2, 3), 2)   # 6561 < 216 * 49 = 10584, group order 7^5
        # r = 3: |S|^24 < (p - 1)^7 p^(4k)
        self.assertEqual(hc.least_k(2, 3, 2), 7)
        self.assertEqual(hc.least_k(3, 3, 2), 3)   # group order 3^7 = 2187
        self.assertEqual(hc.least_k(7, 3, 3), 2)
        self.assertEqual(hc.least_k(2, 4, 2), 6)
        # k = 1 (the Heisenberg group mod p itself) never fails in this family for small r
        for p in (2, 3, 5, 7, 11, 13):
            for r in (2, 3, 4):
                self.assertFalse(hc.abelian_bound_fails(p, 1, r, len(hc.difference_cover(p))), (p, r))

    def test_counting_and_derived_bounds(self):
        for p in (2, 3, 7):
            s = len(hc.difference_cover(p))
            for k in range(1, 12):
                for r in range(1, 6):
                    ks, ds = hc.sizes(p, k, r, s)
                    self.assertLessEqual(ds, ks ** (r + 1))  # Proposition 5(a)
                    self.assertTrue(hc.derived_bound_holds(ks, ds, p ** k, r), (p, k, r))  # Theorem 9'

    def test_prop6_s3(self):
        s3_inv = lambda x: tuple(sorted(range(3), key=lambda i: x[i]))
        ks, ds, isz, ok = hc.prop6_instance(hc.s3_mul, s3_inv, (0, 1, 2), [(0, 1, 2), (1, 0, 2)],
                                            (2, 1, 0), 2)
        self.assertEqual((ks, ds, isz, ok), (4, 8, 1, True))
        self.assertEqual(hc.least_power(2, 1, 2), 9)

    def test_prop6_q8_squared(self):
        m2 = hc.power_mul(hc.q8_mul)
        one = ((1, 0), (1, 0))
        L = hc.closure(m2, [((1, 1), (1, 2))], one)
        self.assertEqual(len(L), 4)
        inv2 = lambda x: tuple((s, 0) if u == 0 else (-s, u) for s, u in x)
        ks, ds, isz, ok = hc.prop6_instance(m2, inv2, one, L, ((1, 2), (1, 0)), 3)
        self.assertEqual((ks, ds, isz, ok), (8, 128, 2, True))
        self.assertEqual(hc.least_power(4, 2, 3), 25)
        self.assertIsNone(hc.least_power(4, 2, 2))  # lambda = 1/2 is too big for r = 2


if __name__ == "__main__":
    unittest.main()
