# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import hamiltonian_cubes as hc


class GroupTests(unittest.TestCase):
    def test_q8(self):
        for a in range(8):
            self.assertEqual(hc.Q8[a][hc.q8_inv(a)], 0)
            for b in range(8):
                for c in range(8):
                    self.assertEqual(hc.Q8[hc.Q8[a][b]][c], hc.Q8[a][hc.Q8[b][c]])
        self.assertEqual(hc.Q8[hc.I_][hc.J_], hc.K_)
        self.assertEqual(hc.Q8[hc.J_][hc.I_], hc.K_ + 4)
        self.assertEqual(hc.Q8[hc.I_][hc.I_], 4)

    def test_q8_z2(self):
        t = hc.q8_z2_table()
        for a in range(16):
            for b in range(16):
                for c in range(16):
                    self.assertEqual(t[t[a][b]][c], t[a][t[b][c]])

    def test_q8_subgroups(self):
        subs = hc.all_subgroups(1)
        self.assertEqual(sorted(len(L) for L in subs), [1, 2, 4, 4, 4, 8])
        s = hc.lemma_summary(subs, 1)
        self.assertTrue(s["centre_bound_holds"])
        self.assertTrue(s["intersection_bound_holds"])


class DiagonalTests(unittest.TestCase):
    def test_r2(self):
        L, y = hc.diagonal_example()
        ks, ds, isz, ok = hc.prop6_instance(L, y, 2)
        self.assertEqual((len(L), isz, ks, ds, ok), (8, 2, 16, 256, True))
        # The lemma's bound |I|^3 >= |L| holds with equality, and Theorem 9 still holds.
        self.assertEqual(isz ** 3, len(L))
        self.assertFalse(hc.abelian_bound_fails_sizes(ks, ds, 2))

    def test_r3(self):
        L, y = hc.diagonal_example()
        self.assertEqual(hc.prop6_instance(L, y, 3), (16, 2048, 2, True))

    def test_lemma_data(self):
        L, _ = hc.diagonal_example()
        self.assertEqual(hc.lemma_data(L, 3), (8, 2, 2))

    def test_least_powers(self):
        self.assertIsNone(hc.least_power(8, 2, 2))
        self.assertEqual(hc.least_power(8, 2, 3), 5)
        self.assertEqual(hc.least_power(8, 2, 4), 4)
        self.assertEqual(hc.least_power(8, 2, 5), 4)
        # Q_8^15, r = 3: |K| = 2^16, |D| = 2^55 and 16 * 24 < 55 * 7; Q_8^12 still holds.
        self.assertTrue(hc.abelian_bound_fails_sizes(2 ** 16, 2 ** 55, 3))
        self.assertFalse(hc.abelian_bound_fails_sizes(2 ** 13, 2 ** 44, 3))


class Theorem9Tests(unittest.TestCase):
    def test_abelian_sanity(self):
        table = [[a ^ b for b in range(8)] for a in range(8)]
        self.assertEqual(hc.served_pairs(table, list(range(8))), 64)
        self.assertEqual(hc.theorem9_r2_exhaustive(table)["violations"], 0)

    def test_small_set(self):
        # K = {1, i} in Q_8 serves (1,1), (1,i), (i,1), (1,-i), (-i,1).
        self.assertEqual(hc.served_pairs(hc.Q8, [0, hc.I_]), 5)


if __name__ == "__main__":
    unittest.main()
