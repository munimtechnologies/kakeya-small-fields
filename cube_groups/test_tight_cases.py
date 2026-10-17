# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import m6_sharp as ms
import question_r as qr
import tight_cases as tc


class TestNormalForms(unittest.TestCase):
    def test_small(self):
        self.assertEqual(tc.normal_forms(4, 2), [("x0_not_in_R_d0", [4, 8]), ("x0_in_R_d1", [1, 4]),
                                                 ("x0_not_in_R_d1", [2, 4]), ("x0_in_R_d2", [1, 2])])
        self.assertEqual(tc.normal_forms(5, 2)[2], ("x0_not_in_R_d1", [2, 4, 8]))
        self.assertEqual([len(tc.normal_forms(t, k)) for t, k in tc.PLAN],
                         [3, 4, 3, 4, 5, 3, 6, 5, 3])

    def test_shape(self):
        # each R has dimension t - k, contains x0 = e_0 exactly for the "in" forms, and meets
        # X_1 = span(e_0, ..., e_(k-1)) in dimension d
        for t, k in tc.PLAN:
            X1 = qr.span([1 << i for i in range(k)])
            for name, Rb in tc.normal_forms(t, k):
                R = qr.span(Rb)
                self.assertEqual(ms.rank_f2(Rb), t - k)
                self.assertEqual(1 in R, "_in_R" in name and "not" not in name)
                self.assertEqual(len(R & X1), 1 << int(name.rsplit("_d", 1)[1]))


class TestLemma33(unittest.TestCase):
    def test_below_2k(self):
        # t < 2k: K_v lies in R, of dimension t - k < k, so no A_v has rank <= t - k at all.
        # candidates = forms x |R|^(t - 1)
        expected = {(3, 2): 12, (4, 3): 24, (5, 3): 1280, (5, 4): 48, (6, 4): 5120, (6, 5): 96}
        for (t, k), cand in expected.items():
            s = tc.lemma33(t, k)
            self.assertEqual((s["candidates_v"], s["low_rank_v"], s["survivors"]), (cand, 0, 0))
            self.assertEqual(s["hyp_fail"], 0)

    def test_at_2k(self):
        # t = 2k: rank <= k forces K_v = R, so x0 is not in R and A_v kills the unit vectors that
        # span R; the other k - 1 columns of A_v are free (|R|^(k-1) choices) in each of the k forms
        # with x0 not in R. Every such A_v fails with every A_u: the pair argument is needed.
        for t, k, cand, low, gl in ((4, 2, 256, 8, 6), (6, 3, 196608, 192, 168)):
            s = tc.lemma33(t, k)
            self.assertEqual((s["candidates_v"], s["low_rank_v"], s["pairs"]), (cand, low, low * gl))
            self.assertEqual((s["survivors"], s["hyp_fail"]), (0, 0))

    def test_t5_k2(self):
        s = tc.lemma33(5, 2)
        self.assertEqual(s["candidates_v"], 4 * 8 ** 4)
        self.assertEqual(s["hyp_fail"], 0)
        self.assertEqual(s["fail"], {})
        self.assertGreater(s["survivors"], 0)

    def test_example(self):
        # The example of notes/question-r.md: x0 = e_0, X_1 = span(e_0, e_1), R = span(e_1, e_2, e_3).
        Au = qr.from_columns([0, 0, 4, 8, 2], 5)
        Av = qr.from_columns([1, 0, 0, 8, 16], 5)
        R = qr.span([2, 4, 8])
        self.assertTrue(all(tc.hypotheses(Au, Av, R, 5, 2).values()))
        self.assertTrue(all(tc.conclusions(Au, Av, R, 5, 2).values()))
        self.assertEqual(qr.kernel(Av, 5) & qr.kernel(Au ^ Av, 5), {0, 2})

    def test_image_hypothesis_needed(self):
        # t = 4, k = 2, R = span(e_2, e_3): A_v = (e_0, 0, e_2, 0) and A_w = (e_0, 0, 0, e_3) have
        # rank 2, but (I + A_v) e_1 = e_1 is not in R, and t < 2k + 1.
        Au = qr.from_columns([0, 0, 4, 8], 4)
        Av = qr.from_columns([1, 0, 4, 0], 4)
        h = tc.hypotheses(Au, Av, qr.span([4, 8]), 4, 2)
        self.assertEqual([key for key, ok in h.items() if not ok], ["image_I_v"])


if __name__ == "__main__":
    unittest.main()
