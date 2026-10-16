# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

from fibre import (Tensor, agl_control, b_values, brute_b, fibre, gamma, lossy_pairs, max_class,
                   order_slack, predicted, random_law, random_laws, served_all, set_search,
                   small_groups, tensor_design)


class TestPeeling(unittest.TestCase):
    def test_loss_counts(self):
        # L(sigma) of Theorem 27: 321 0, 312 1, 231 2, 213 3, 132 3, 123 4; r = 2: 21 0, 12 1
        got = [len(lossy_pairs(3, tuple(int(c) for c in s))) for s in ("321", "312", "231", "213", "132", "123")]
        self.assertEqual(got, [0, 1, 2, 3, 3, 4])
        self.assertEqual([len(lossy_pairs(2, s)) for s in ((2, 1), (1, 2))], [0, 1])
        self.assertEqual(lossy_pairs(3, (2, 1, 3)), [(2, (3,)), (2, (3,)), (1, (3,))])

    def test_random_laws(self):
        rng = random.Random(1)
        for name in ("S_3", "Q_8"):
            T = small_groups()[name]
            for r in (2, 3):
                self.assertGreaterEqual(random_laws(T, rng, r, 40), -1e-9, (name, r))

    def test_abelian_lossless(self):
        T, rng = [[(a + b) % 6 for b in range(6)] for a in range(6)], random.Random(2)
        for _ in range(30):
            law = random_law(6, 3, rng, 8)
            self.assertGreaterEqual(order_slack(T, law, (1, 2, 3)), -1e-9)


class TestSetForms(unittest.TestCase):
    def test_exhaustive_s3(self):
        for r in (2, 3):
            out = set_search(small_groups()["S_3"], random.Random(3), r)
            self.assertEqual(out["sets"], 63)
            self.assertEqual(out["violations"], 0)
            self.assertEqual(out["not_dominated"], 0)

    def test_q8_whole_group(self):
        T = small_groups()["Q_8"]
        D = sorted(served_all(T, frozenset(range(8)), 2))
        self.assertEqual(len(D), 64)
        self.assertEqual(fibre(T, D, 1, (2,)), 2)                # c = d_2^-1 d_1 d_2: d_1 in {c, c^-1}
        self.assertEqual(gamma(T, D, 1, (2,)), 2)
        self.assertGreaterEqual(8 ** 8 * 2, 64 ** 3)

    def test_agl_control(self):
        out = agl_control()
        self.assertEqual((out["K"], out["D"], out["fibre"]), (32, 4352, 16))
        self.assertTrue(out["fails_without_loss"])
        self.assertGreaterEqual(out["slack_12_with_fibre_loss"], -1e-9)
        self.assertTrue(out["set_form_holds"] and out["dominated"])


class TestTensor(unittest.TestCase):
    def test_group_law(self):
        rng = random.Random(4)
        for p, j, k in ((2, 2, 2), (3, 2, 1)):
            G = Tensor(p, j, k)
            elems = G.elements()
            for _ in range(200):
                a, b, c = rng.choice(elems), rng.choice(elems), rng.choice(elems)
                self.assertEqual(G.mul(G.mul(a, b), c), G.mul(a, G.mul(b, c)))
                self.assertEqual(G.mul(a, G.inv(a)), G.one)
                expect = tuple((x - y) % p for x, y in zip(G.ten(a[0], b[1]), G.ten(b[0], a[1])))
                self.assertEqual(G.comm(a, b), (G.one[0], G.one[1], expect))

    def test_b_by_rank_equals_brute(self):
        for p, j, k in ((2, 2, 1), (2, 2, 2), (3, 2, 1)):
            G = Tensor(p, j, k)
            self.assertEqual(b_values(G)[0], brute_b(G))
            self.assertEqual(b_values(G), (p ** (j + k - 1), p ** k))

    def test_designs(self):
        rng = random.Random(5)
        table = {(2, 2, 1): (6, 14, 2, 4, 4), (2, 2, 2): (12, 52, 4, 10, 8), (3, 2, 1): (9, 57, 3, 7, 9),
                 (2, 3, 3): (32, 392, 8, 43, 32), (3, 2, 2): (27, 495, 9, 25, 27)}
        for (p, j, k), (kk, diffs, beta, gam, b) in table.items():
            res = tensor_design(p, j, k, rng, sample=60)
            pr = predicted(p, j, k)
            self.assertEqual((pr["K"], pr["K^-1K"], pr["beta"], pr["gamma"], pr["b"]), (kk, diffs, beta, gam, b))
            self.assertEqual((res["K"], res["K^-1K"], res["beta"], res["gamma"], res["b"]), (kk, diffs, beta, gam, b))
            self.assertTrue(res["matches"])
            self.assertEqual(res["unserved_in_sample"], 0)
            self.assertTrue(res["beta25_holds"])
            self.assertFalse(res["abelian25_fails"])               # too small for the genuine-loss regime

    def test_small_group_b(self):
        self.assertEqual([max_class(small_groups()[n]) for n in ("S_3", "Q_8", "S_4")], [3, 2, 8])


if __name__ == "__main__":
    unittest.main()
