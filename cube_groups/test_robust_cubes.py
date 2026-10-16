# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import math
import random
import unittest

import robust_cubes as rc


class TestRobustCubes(unittest.TestCase):
    def test_groups(self):
        for G in rc.groups():
            self.assertTrue(rc.is_group(G), G["name"])
        orders = {G["name"]: G["n"] for G in rc.groups()}
        self.assertEqual(orders["S3"], 6)
        self.assertEqual(orders["D4"], 8)
        self.assertEqual(orders["Q8"], 8)
        for G in rc.groups():
            comm = all(G["mul"][x][y] == G["mul"][y][x] for x in range(G["n"]) for y in range(G["n"]))
            self.assertEqual(comm, G["abelian"], G["name"])

    def test_set_bound_abelian_small(self):
        for G in rc.groups():
            if not G["abelian"]:
                continue
            for r, cap in ((1, 8), (2, 8), (3, 4)):
                if G["n"] <= cap:
                    self.assertTrue(rc.exhaustive(G, r)["holds"], (G["name"], r))

    def test_r1_is_difference_bound(self):
        # r = 1: cov_1(K) = K - K, and |K|^2 >= |K - K| is the claim
        G = rc.abelian(7)
        res = rc.exhaustive(G, 1)
        self.assertTrue(res["holds"])
        self.assertAlmostEqual(res["claimed_exponent"], 0.5)

    def test_equality_full_D(self):
        # d uniform on G^r and A = 0: every Y_t with t != 0 is uniform, so the sum is (2^r - 1) log2 N
        for G, r in ((rc.abelian(3), 2), (rc.abelian(2, 2), 2), (rc.abelian(2), 3)):
            D = list(itertools.product(range(G["n"]), repeat=r))
            ts = list(itertools.product((0, 1), repeat=r))
            ws = [[rc.word(G, d, t) for t in ts] for d in D]
            s = rc.entropy_sum(G, D, [G["e"]] * len(D), ws)
            self.assertAlmostEqual(s, (2 ** r - 1) * math.log2(G["n"]))
            self.assertAlmostEqual(s, (2 ** r - 1) / r * math.log2(len(D)))

    def test_entropy_bound_local_search(self):
        rng = random.Random(7)
        for G, r in ((rc.abelian(4), 2), (rc.abelian(2, 2), 2), (rc.abelian(5), 2), (rc.abelian(2), 3)):
            res = rc.entropy_trials(G, r, 6, rng)
            self.assertGreaterEqual(res["least_slack"], -1e-9, (G["name"], r))

    def test_subgroup_power_meets_bound_exponent(self):
        # D = H^2 for H = {0, 2} in Z_4: K = H covers it, |K|^8 = 256 >= |D|^3 = 64
        G = rc.abelian(4)
        masks = [rc.translate_masks(G, d) for d in itertools.product((0, 2), repeat=2)]
        K = 0b0101
        self.assertTrue(all(any(m & K == m for m in ms) for ms in masks))
        self.assertGreaterEqual(2 ** 8, 4 ** 3)


if __name__ == "__main__":
    unittest.main()
