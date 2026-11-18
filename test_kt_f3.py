# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""Tests for kt_f3.py (note a180). Every assertion is a fact proved in notes/a180.md, an
exact arithmetic comparison quoted there, or a consistency check of transcribed constants."""
import itertools
import math
import random
import unittest
from fractions import Fraction

import kt_f3 as T

LOG2_3 = math.log2(3)


class TestKatzTaoF3(unittest.TestCase):

    def test_lemma_143_random_distributions(self):
        # Lemma 143: 5H(X,Y) + H(X-Y) <= 4H(X) + 4H(Y) + 3H(X+Y) in every abelian group.
        rng = random.Random(180)
        for m, d in [(3, 1), (3, 2), (5, 1), (2, 2), (9, 1), (7, 1)]:
            for _ in range(60):
                joint = T.random_joint(m, d, rng.randint(1, 14), rng)
                self.assertGreaterEqual(T.kt_slack(joint, m), -1e-9)

    def test_kakeya_specialization_on_maps(self):
        # Proof of Theorem 68 / Corollary 68.1: for Y_t = P(X) + tX, X uniform on F_3^k,
        # H(Ya - Yb) = H(Ya, Yb) = k log2 3 and 6 k log2 3 <= 4H(Ya) + 4H(Yb) + 3H(Ya + Yb).
        rng = random.Random(181)
        for k in (1, 2):
            vecs = T.f3_vectors(k)
            for trial in range(40):
                P = T.frame_map(k) if trial == 0 else T.random_map(k, rng)
                for a, b in [(0, 1), (1, 2), (2, 0), (1, 0)]:
                    joint = {}
                    for x in vecs:
                        ya = tuple((p + a * u) % 3 for p, u in zip(P[x], x))
                        yb = tuple((p + b * u) % 3 for p, u in zip(P[x], x))
                        joint[(ya, yb)] = joint.get((ya, yb), 0) + 1
                    n = k * LOG2_3
                    self.assertAlmostEqual(T.entropy(joint), n, places=9)
                    hd = T.entropy(T.marginal(joint, lambda key: T.vsub(key[0], key[1], 3)))
                    self.assertAlmostEqual(hd, n, places=9)
                    ha = T.entropy(T.marginal(joint, lambda key: key[0]))
                    hb = T.entropy(T.marginal(joint, lambda key: key[1]))
                    hs = T.entropy(T.marginal(joint, lambda key: T.vadd(key[0], key[1], 3)))
                    self.assertLessEqual(6 * n, 4 * ha + 4 * hb + 3 * hs + 1e-9)

    def test_frame_products_have_lambda_exactly_2k(self):
        for k in (1, 2, 3):
            self.assertEqual(T.fibre_product(T.frame_map(k), k), 2 ** (2 * k * 3 ** k))
            self.assertTrue(T.satisfies_corollary_68_1(T.frame_map(k), k))

    def test_corollary_68_1_all_maps_k1(self):
        vecs = T.f3_vectors(1)
        count = 0
        for images in itertools.product(vecs, repeat=len(vecs)):
            P = dict(zip(vecs, images))
            self.assertTrue(T.satisfies_corollary_68_1(P, 1))
            count += 1
        self.assertEqual(count, 27)

    def test_corollary_68_1_random_and_constant_maps(self):
        rng = random.Random(182)
        for k, trials in ((2, 300), (3, 60)):
            for _ in range(trials):
                self.assertTrue(T.satisfies_corollary_68_1(T.random_map(k, rng), k))
            zero = tuple([0] * k)
            const = {x: zero for x in T.f3_vectors(k)}
            self.assertTrue(T.satisfies_corollary_68_1(const, k))

    def test_theorem_68_on_every_kakeya_set_in_the_plane(self):
        pts = T.f3_vectors(2)
        sizes = []
        for mask in range(1 << 9):
            K = {pts[i] for i in range(9) if mask >> i & 1}
            if T.is_kakeya_f3(K, 2):
                sizes.append(len(K))
                self.assertTrue(T.theorem_68_holds(len(K), 2))
        # The smallest Kakeya set in F_3^2 has 7 points (KLSS; a180 Remark 68.5).
        self.assertEqual(min(sizes), 7)
        self.assertTrue(T.is_kakeya_f3(set(T.f3_vectors(3)), 3))
        self.assertTrue(T.theorem_68_holds(27, 3))

    def test_exact_comparisons_quoted_in_the_note(self):
        # 3^(6/11) > 9/5  <=>  3^6 * 5^11 > 9^11.
        self.assertGreater(3 ** 6 * 5 ** 11, 9 ** 11)
        # 3^(6/11) < 1.8899 (consistent with the known upper bound).
        self.assertLess(3 ** 6 * 10000 ** 11, 18899 ** 11)
        # (15/11) log2 3 < 3 log2(5/3)  <=>  3^48 < 5^33.
        self.assertLess(3 ** 48, 5 ** 33)
        # The bound overtakes Bukh-Chao's 3^n / (5/3)^(n-1) exactly from n = 45 on.
        self.assertEqual(T.first_n_beating_bukh_chao(), 45)
        self.assertTrue(all(T.beats_bukh_chao(n) for n in range(45, 201)))
        self.assertFalse(any(T.beats_bukh_chao(n) for n in range(1, 45)))

    def test_transcribed_constants_from_arxiv_2611_19594(self):
        num = 80908638342740092 + 74518340847137328 + 53930565379970708
        self.assertEqual(num, 209357544569848128)
        self.assertEqual(59 + 52 + 41, 152)
        self.assertEqual(1077 + 962 + 723, 2762)
        inv_c_star = Fraction(114631769327023765, 209357544569848128)
        self.assertGreater(inv_c_star, Fraction(83, 152))
        self.assertGreater(Fraction(83, 152), Fraction(6, 11))
        self.assertGreater(Fraction(1509, 2762), Fraction(6, 11))


if __name__ == "__main__":
    unittest.main()
