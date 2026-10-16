# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import math
import random
import unittest
from fractions import Fraction

from prop31_cubes import groups, inverses
from theorem29 import (comm, commuting_law, exhaustive, gamma_product, gpk_design, gpk_excess,
                       named_groups, peeling_lp, proposition28, served_all, tensor_design,
                       theorem29_slack)
from twosided import commutator_subgroup, max_class


class TestBasics(unittest.TestCase):
    def test_commutator_convention(self):
        T = groups()["S_3"]
        inv = inverses(T)
        for a in range(6):
            for b in range(6):
                c = comm(T, inv, a, b)
                self.assertEqual(T[T[b][a]][c], T[a][b])             # b a [a, b] = a b

    def test_commuting_law(self):
        T, rng = groups()["Q_8"], random.Random(0)
        for r in (3, 4):
            for _, o in commuting_law(T, r, rng, 20):
                late = o[2:]
                self.assertTrue(all(T[x][y] == T[y][x] for x in late for y in late))

    def test_g31(self):
        T = named_groups()["G(3,1)"]
        self.assertEqual((len(T), len(commutator_subgroup(T)), max_class(T)), (27, 3, 3))


class TestTheorem29(unittest.TestCase):
    def test_random_commuting(self):
        rng = random.Random(1)
        for name in ("S_3", "Q_8"):
            T = groups()[name]
            logb = math.log2(max_class(T))
            for trial in range(120):
                law = commuting_law(T, 3 + (trial % 3 == 0), rng, rng.choice((3, 8, 16)))
                self.assertGreaterEqual(theorem29_slack(T, law, logb), -1e-9, name)


class TestSetForms(unittest.TestCase):
    def test_q8_whole_group(self):
        T = groups()["Q_8"]
        D = served_all(T, frozenset(range(8)), 3)
        self.assertEqual(len(D), 512)
        self.assertEqual(gamma_product(T, D), 2 ** 6)
        self.assertGreaterEqual(8 ** 24 * 2 ** 6, 512 ** 7)

    def test_exhaustive_s3(self):
        out = exhaustive(groups()["S_3"], random.Random(2))
        self.assertEqual(out["sets"], 63)
        self.assertEqual(out["thm29p_violations"], 0)
        self.assertEqual(out["thm27b_violations"], 0)
        self.assertGreaterEqual(out["least_slack"][0], -1e-9)


class TestGpk(unittest.TestCase):
    def test_design_sizes(self):
        T, K, D, s = gpk_design(2, 1)
        self.assertEqual((len(T), len(K), len(D), s), (8, 4, 16, 2))

    def test_excess_p2(self):
        for k in (1, 2):
            res = gpk_excess(2, k)
            self.assertTrue(res["lhs_le_cap"])
            got = [round(res["orders"][s]["excess"] + 8, 9) for s in ("321", "312", "231", "213", "132", "123")]
            self.assertEqual(got, [0, k, 0, k, 3 * k, 3 * k])
            self.assertTrue(all(v["peeling_holds"] for v in res["orders"].values()))


class TestProposition28(unittest.TestCase):
    def test_small_groups(self):
        for name in ("S_3", "Q_8"):
            out = proposition28(groups()[name], random.Random(3), sample=20)
            self.assertGreater(out["designs"], 0)
            self.assertEqual(out["unserved"], 0, name)
            self.assertEqual(out["violations_derived"], 0, name)
            self.assertEqual(out["violations_b"], 0, name)
            self.assertTrue(out["double_coset_ok"], name)


class TestTensor(unittest.TestCase):
    def test_p2_k2(self):
        res = tensor_design(2, 2, random.Random(5), sample=50)
        self.assertEqual(res["order"], 256)
        self.assertEqual([res["K"], res["K^-1K"], res["b"], res["derived"]], res["predicted"])
        self.assertEqual(res["predicted"], [12, 52, 8, 16])
        self.assertTrue(res["generates_G"])
        self.assertEqual(res["unserved_in_sample"], 0)
        self.assertTrue(res["thm25_b_holds"] and res["thm29_b_holds"])


class TestLP(unittest.TestCase):
    def test_lambda_half(self):
        best, points, dual = peeling_lp(Fraction(1, 2))
        self.assertEqual(best, 5)
        self.assertEqual(dual, 5)
        self.assertEqual(points, [(Fraction(5, 7), Fraction(8, 7))])

    def test_lambda_zero_is_gpk(self):
        best, points, dual = peeling_lp(0)
        self.assertEqual((best, dual, points), (4, 4, [(1, 1)]))


if __name__ == "__main__":
    unittest.main()
