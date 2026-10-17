# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import case_b as cb
import sat_aniso as sa


class TestLemma34(unittest.TestCase):
    def test_counts(self):
        # By hand: sigma(e_1), sigma(e_2) independent with beta = 0 (alpha = 0), beta = sigma(e_1)
        # or beta = sigma(e_2) (one alpha each): 6 + 12; sigma(e_1) = sigma(e_2) = a with beta
        # outside span(a) (one alpha each): 3 x 2 = 6. Type (i) is the first 6, type (ii) the rest.
        self.assertEqual(cb.lemma34(), {"candidates": 9216, "systems": 24, "i": 6, "ii": 18,
                                        "other": 0})


class TestNormalForm(unittest.TestCase):
    def test_example(self):
        As, ss, B = cb.example_t2()
        at, sv = sa.tables(As, ss, B, 2)
        self.assertTrue(sa.is_system(at, sv, 2, 2) and sa.anisotropic(sv))
        self.assertTrue(cb.in_normal_form(As, ss, B, 2, 1))
        self.assertTrue(cb.accepts(As, ss, B, 2, 1))
        # u = 1 and u + f = 3 qualify; f = 2 does not (beta(f, V) = span(e_1) contains sigma(f))
        self.assertEqual([u for u in (1, 2, 3) if cb.qualifies(at, sv, 2, 2, 1, u)], [1, 3])

    def test_not_in_normal_form(self):
        # the example with the basis of V swapped is still an anisotropic system, but sigma(v_0) = e_1
        As, ss, B = [0, 8], [2, 1], {(0, 1): 2}
        at, sv = sa.tables(As, ss, B, 2)
        self.assertTrue(sa.is_system(at, sv, 2, 2) and sa.anisotropic(sv))
        self.assertFalse(cb.in_normal_form(As, ss, B, 2, 1))
        self.assertFalse(cb.accepts(As, ss, B, 2, 1))

    def test_wanted_phi(self):
        self.assertEqual([cb.wanted_phi(i, 3) for i in range(1, 8)], [0, 0, 2, 4, 8, 16, 32])
        self.assertEqual([cb.wanted_phi(i, 4) for i in range(1, 10)], [0, 0, 0, 2, 4, 8, 16, 32, 64])

    def test_unit_clauses(self):
        # t units for sigma(v_0), t k for the zero columns of A_(v_0), (d - 1) t for phi
        for t, k in ((2, 1), (3, 2), (4, 2)):
            d = t + k - 1
            base, _ = sa.encode(t, d, echelon=False)
            cnf, _ = cb.encode_case_b(t, k)
            self.assertEqual(cnf.nv, base.nv)
            self.assertEqual(len(cnf.clauses) - len(base.clauses), t + t * k + (d - 1) * t)

    def test_normalisation(self):
        n = cb.normalisation_check(random.Random(7), 10)
        self.assertEqual(n["qualifying"], [2])
        self.assertEqual((n["normal_form"], n["accepted"]), (20, 20))
        self.assertEqual(n["disagree"], 0)
        self.assertLess(n["mutations_accepted"], n["mutations"])


if __name__ == "__main__":
    unittest.main()
