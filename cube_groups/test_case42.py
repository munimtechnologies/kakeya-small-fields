# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import unittest

import case42


class TestHelpers(unittest.TestCase):
    def test_nullspace(self):
        self.assertEqual(case42.nullspace([0b11], 2), [0b11])
        self.assertEqual(case42.nullspace([], 3), [1, 2, 4])
        for C in range(1, 16):
            basis = case42.nullspace([C], 4)
            self.assertEqual(len(basis), 3)
            self.assertTrue(all(not case42.parity(C & v) for v in basis))
            self.assertEqual(case42.rank_f2(basis), 3)

    def test_apply(self):
        # M = [[1,0],[1,1]]: row 0 = 0b01, row 1 = 0b11, so M = 0b01 | 0b11 << 2
        M = 0b01 | (0b11 << 2)
        self.assertEqual(case42.apply(M, 0b01, 2, 2), 0b11)
        self.assertEqual(case42.apply(M, 0b10, 2, 2), 0b10)

    def test_full_hom_matches_hommap(self):
        # b = 1: symmetric zero-diagonal matrices; b >= 2: nothing (Theorem 18's lemma)
        for a in range(1, 5):
            self.assertEqual(case42.lam_dim(case42.full_basis(a, 1), a, 1), a * (a - 1) // 2)
        for a, b in [(2, 2), (3, 2), (2, 3)]:
            self.assertEqual(case42.kernel_dim(case42.full_basis(a, b), a, b), 0)
            self.assertEqual(case42.lam_dim(case42.full_basis(a, b), a, b), 0)
            self.assertEqual(case42.lam_dim(case42.full_basis(a, b), a, b, diagonal=False), 0)


class TestProposition18(unittest.TestCase):
    def test_hyperplanes_2_2(self):
        r = case42.hyperplane_report(2, 2)
        self.assertEqual(r["hyperplanes"], 15)
        self.assertEqual(r["kernel_zero"], 15)
        self.assertEqual(r["lam_zero"], 15)
        self.assertEqual(r["polar_one"], 9)           # the 9 rank-1 matrices C
        self.assertEqual(r["polar_match"], 15)

    def test_hyperplanes_2_3(self):
        r = case42.hyperplane_report(2, 3)
        self.assertEqual(r["lam_zero"], r["hyperplanes"])
        self.assertEqual(r["polar_one"], 0)

    def test_lemma16(self):
        self.assertTrue(case42.lemma16_ok(2, 2))
        self.assertTrue(case42.lemma16_ok(2, 3))
        self.assertTrue(case42.lemma16_ok(1, 2))

    def test_codim2_count(self):
        self.assertEqual(sum(case42.codim2_report(2, 2).values()), 35)


class TestLemma15(unittest.TestCase):
    def test_small(self):
        for n in range(1, 4):
            self.assertEqual(case42.lemma15_check(n)["violations"], 0)
        self.assertGreater(case42.lemma15_check(2)["with_B_nonzero"], 0)

    def test_normal_form(self):
        # q = t1 (1 + t2) = x0 + x0 x1 with pi = t2 solves the equation
        T, Brow = case42.tables(0b101, 2)
        self.assertTrue(case42.solves(T, Brow, 0b10, 2))

    def test_rank4_control(self):
        # q = x0 x1 + x2 x3 has polar rank 4: no linear form pi solves the equation
        T, Brow = case42.tables((1 << 4) | (1 << 9), 4)
        self.assertEqual(case42.form_rank(Brow, 4), 4)
        self.assertFalse(any(case42.solves(T, Brow, pm, 4) for pm in range(16)))

    def test_vector_form(self):
        r = case42.vector_check(2, 2)
        self.assertGreater(r["solutions"], 0)
        self.assertEqual(r["outside_span"], 0)


class TestWitt(unittest.TestCase):
    def test_small(self):
        for m in range(1, 4):
            self.assertEqual(case42.witt_check(m)["violations"], 0)


if __name__ == "__main__":
    unittest.main()
