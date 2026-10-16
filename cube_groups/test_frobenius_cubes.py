# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import unittest

import frobenius_cubes as fc


class TestFrobeniusCubes(unittest.TestCase):
    def test_group_axioms(self):
        for q in (3, 5, 7):
            G = fc.group(q)
            self.assertEqual(len(G), q * (q - 1))
            e = (1, 0)
            for x in G:
                self.assertEqual(fc.mul(q, x, fc.inv(q, x)), e)
                self.assertEqual(fc.mul(q, e, x), x)
            for x, y, z in itertools.product(G, repeat=3):
                self.assertEqual(fc.mul(q, fc.mul(q, x, y), z), fc.mul(q, x, fc.mul(q, y, z)))
        # non-abelian: (2, 0)(1, 1) = (2, 2) but (1, 1)(2, 0) = (2, 1)
        self.assertNotEqual(fc.mul(5, (2, 0), (1, 1)), fc.mul(5, (1, 1), (2, 0)))

    def test_brute_cover(self):
        for q, r in ((3, 2), (5, 2), (5, 3), (7, 2)):
            self.assertTrue(fc.brute_cover(q, r), (q, r))

    def test_reduction(self):
        for q in (3, 5, 7, 11, 67):
            self.assertTrue(fc.reduction_holds(q), q)

    def test_reduction_implies_cover_where_both_run(self):
        for q in (3, 5, 7):
            self.assertEqual(fc.reduction_holds(q), fc.brute_cover(q, 2))

    def test_abelian_bound_fails(self):
        # r = 2: 256 (q - 1)^2 < q^3; q = 257 gives 2^24 < 257^3, q = 251 does not
        self.assertTrue(fc.is_prime(257) and fc.is_prime(251) and fc.is_prime(4099))
        self.assertTrue(fc.abelian_bound_fails(257, 2))
        self.assertFalse(fc.abelian_bound_fails(251, 2))
        self.assertEqual(fc.least_failing_prime(2), 257)
        # r = 3: 2^24 (q - 1)^3 < q^7; true at q = 67, false at q = 61
        self.assertTrue(fc.abelian_bound_fails(67, 3))
        self.assertFalse(fc.abelian_bound_fails(61, 3))
        self.assertEqual(fc.least_failing_prime(3), 67)

    def test_counting_bound(self):
        # |D| <= |K|^(r+1) in every group; here |D| / |K|^(r+1) = q / (2^(r+1) (q - 1))
        for q in (3, 5, 67, 257, 4099):
            for r in range(1, 7):
                self.assertTrue(fc.counting_bound_holds(q, r), (q, r))
                k, dsize = fc.sizes(q, r)
                self.assertLessEqual(k, 2 * dsize ** (1 / (r + 1)) + 1e-9)


if __name__ == "__main__":
    unittest.main()
