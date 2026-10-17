# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m6_sharp as ms
import question_r as qr


class TestLemma31(unittest.TestCase):
    def test_diagonal(self):
        # Lemma 23(d): u = (a = 0, b = e_0) has sigma(u) = e_0 and beta(u, (a', b')) = a'_0 e_0, so
        # every v with a'_0 = 1 gives a pair with sigma(u) != 0.
        for t in (2, 3):
            m, at, sv = ms.diagonal(t)
            self.assertTrue(ms.is_system(at, sv, m, t))
            pairs, nontrivial, fails = qr.lemma31_check(at, sv, m, t)
            self.assertEqual(fails, 0)
            self.assertGreater(nontrivial, 0)

    def test_random(self):
        rng = random.Random(7)
        for t in (3, 4):
            for m, at, sv in qr.random_systems(rng, t, 6, max_m=4):
                self.assertTrue(ms.is_system(at, sv, m, t))
                self.assertEqual(qr.lemma31_check(at, sv, m, t)[2], 0)

    def test_control(self):
        st = qr.control(random.Random(5), count=40)
        self.assertEqual(st["systems"], 0)
        self.assertGreaterEqual(st["broken"], 10)


class TestLemma32(unittest.TestCase):
    def test_helpers(self):
        self.assertEqual(qr.from_columns([1, 0, 2], 3), ms.entries(3, [(0, 0), (1, 2)]))
        self.assertEqual(qr.span([2, 4]), {0, 2, 4, 6})
        self.assertEqual(qr.kernel(qr.from_columns([0, 0, 2], 3), 3), {0, 1, 2, 3})
        self.assertEqual(len(qr.ordered_bases([2, 4, 8])), 168)
        self.assertEqual(qr.normal_forms(5), [("x0_not_in_R", [2, 4, 8]), ("x0_in_R", [1, 2, 4])])

    def test_small_t(self):
        # t = 3: one form, one A_u, 2 A_v. t = 4: two forms, 6 A_u each, 16 A_v each.
        s3, s4 = qr.lemma32(3), qr.lemma32(4)
        self.assertEqual((s3["pairs"], s4["pairs"]), (2, 192))
        self.assertEqual((s3["hyp_fail"], s4["hyp_fail"]), (0, 0))
        self.assertEqual((s3["survivors"], s4["survivors"]), (0, 0))

    def test_t5(self):
        s = qr.lemma32(5)
        self.assertEqual(s["pairs"], 2 * 168 * 512)
        self.assertEqual(s["hyp_fail"], 0)
        self.assertEqual(s["fail"], {})
        self.assertGreater(s["survivors"], 0)

    def test_t5_example(self):
        # x0 = e_0, z = e_1, R = span(e_1, e_2, e_3). A_u kills e_0, e_1, fixes e_2, e_3 and sends e_4
        # to e_1; A_v fixes e_0, e_3, e_4 and kills e_1, e_2. So A_w fixes e_0, e_2, kills e_1, e_3
        # and sends e_4 to e_1 + e_4.
        Au = qr.from_columns([0, 0, 4, 8, 2], 5)
        Av = qr.from_columns([1, 0, 0, 8, 16], 5)
        R = qr.span([2, 4, 8])
        self.assertTrue(all(qr.hypotheses(Au, Av, R, 5).values()))
        checks, dims = qr.conclusions(Au, Av, R, 5)
        self.assertTrue(all(checks.values()))
        self.assertEqual(dims, "3,3")
        self.assertEqual(qr.kernel(Av, 5), {0, 2, 4, 6})
        self.assertEqual(qr.kernel(Au ^ Av, 5), {0, 2, 8, 10})

    def test_t5_hypotheses_needed(self):
        # A_v = the projection onto span(e_0, e_2, e_3, e_4) along e_1: Im(I + A_v) = span(e_1) lies
        # in R, but A_v has rank 4 > 3, so only the rank condition fails.
        Au = qr.from_columns([0, 0, 4, 8, 2], 5)
        Av = qr.from_columns([1, 0, 4, 8, 16], 5)
        h = qr.hypotheses(Au, Av, qr.span([2, 4, 8]), 5)
        self.assertTrue(h["image_I_v"])
        self.assertFalse(h["rank_v"])
        self.assertEqual([k for k, ok in h.items() if not ok], ["rank_v"])


if __name__ == "__main__":
    unittest.main()
