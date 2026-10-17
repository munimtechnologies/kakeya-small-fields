# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import random
import unittest

import m3_core as m3


class TestMatrices(unittest.TestCase):
    def test_good_counts(self):
        # t = 2: the two elements of order 3; t = 3: the 48 elements of order 7.
        self.assertEqual(bin(m3.good_mask(2)).count("1"), 2)
        self.assertEqual(bin(m3.good_mask(3)).count("1"), 48)

    def test_trace_form_nondegenerate(self):
        zm = m3.trace_masks(2)
        self.assertEqual(zm[0], (1 << 16) - 1)
        for B in range(1, 16):
            self.assertEqual(bin(zm[B]).count("1"), 8)

    def test_free_hyperplanes_t2(self):
        # A hyperplane avoiding w and w + I (the order-3 elements) contains I and not w: 7 - 3 = 4.
        hs, fin = m3.free_subspaces(2, 3, m3.trace_masks(2), m3.good_mask(2))
        self.assertTrue(fin)
        self.assertEqual(len(hs), 4)

    def test_stabilisers_t3(self):
        stabs = m3.stabilisers(3)
        gm = m3.good_mask(3)
        self.assertEqual(len(set(stabs)), 14)
        for s in stabs:
            self.assertEqual(bin(s).count("1"), 128)
            self.assertEqual(s & gm, 0)
            self.assertEqual(m3.rank_f2(m3.bits(s)), 7)


class TestVanishing(unittest.TestCase):
    def test_xor_perm(self):
        xm = m3.xor_masks(3)
        self.assertEqual(m3.xor_perm((1 << 1) | (1 << 2), 1, xm), (1 << 0) | (1 << 3))
        self.assertEqual(m3.xor_perm((1 << 1) | (1 << 2), 3, xm), (1 << 1) | (1 << 2))
        self.assertEqual(m3.xor_perm(1 << 5, 6, xm), 1 << 3)

    def test_has_vanishing(self):
        xm = m3.xor_masks(3)
        allnz = (1 << 8) - 2
        self.assertEqual(m3.has_vanishing(allnz, 3, xm), (True, True))
        basis = (1 << 1) | (1 << 2) | (1 << 4)
        self.assertEqual(m3.has_vanishing(basis, 2, xm), (False, True))
        self.assertEqual(m3.has_vanishing(basis, 1, xm), (True, True))
        plane = (1 << 1) | (1 << 2) | (1 << 3)
        self.assertEqual(m3.has_vanishing(plane, 2, xm), (True, True))
        self.assertEqual(m3.least_codim(plane, 3, xm), (1, True))
        self.assertEqual(m3.least_codim(basis, 3, xm), (2, True))
        self.assertEqual(m3.least_codim(0, 3, xm), (3, True))


class TestLemma25(unittest.TestCase):
    def test_lemma25_on_solutions(self):
        # Lemma 25(a), (b) hold for every solution: checked on all of Sol for small systems.
        w = m3.entries(3, [(1, 0), (2, 1), (0, 2), (1, 2)])      # order 7
        cases = [([m3.entries(3, [(0, 0)]), w], 1),
                 ([m3.entries(3, [(0, 0)]), m3.entries(3, [(0, 1), (0, 2), (1, 0), (1, 1)])], 1),
                 ([m3.entries(3, [(0, 1)]), m3.entries(3, [(1, 2)])], 2)]
        for B, y in cases:
            m, at = m3.system(B, y)
            tabs = m3.mon_tables(m)
            sol = m3.solve_sigma(at, m, 3)
            for i in range(1 << len(sol)):
                sv = m3.table(m3.sigma_from_coeffs(m3.combine(sol, i), tabs, 3), m)
                self.assertEqual(m3.lemma25_violations(at, sv, m, 3), (0, 0))

    def test_good_element_zero_and_radical(self):
        # alpha = (w, 0) on F_2^2: Lemma 25(b) forces sigma = 0 on span(e_1) and beta(e_1, .) = 0.
        w = m3.entries(3, [(1, 0), (2, 1), (0, 2), (1, 2)])
        m, at = m3.system([w], 1)
        tabs = m3.mon_tables(m)
        sol = m3.solve_sigma(at, m, 3)
        for i in range(1 << len(sol)):
            sv = m3.table(m3.sigma_from_coeffs(m3.combine(sol, i), tabs, 3), m)
            self.assertEqual(sv[1], 0)
            self.assertEqual(sv[3], sv[2])

    def test_good_complement(self):
        w = m3.entries(3, [(1, 0), (2, 1), (0, 2), (1, 2)])
        s, chosen, bad = m3.good_complement([w, m3.entries(3, [(0, 0)])], 3)
        self.assertGreaterEqual(s, 1)
        self.assertFalse(bad)
        s, chosen, bad = m3.good_complement([m3.entries(3, [(0, 1)])], 3)
        self.assertEqual((s, chosen, bad), (0, [0], False))

    def test_restriction_bound_random(self):
        rng = random.Random(3)
        xms = {m: m3.xor_masks(m) for m in range(1, 6)}
        for _ in range(12):
            c = rng.randint(1, 3)
            B = m3.independent([rng.randrange(1, 512) for _ in range(c)])
            c = len(B)
            y = rng.randint(0, 5 - c) if c < 5 else 0
            m, at = m3.system(B, y)
            tabs = m3.mon_tables(m)
            sol = m3.solve_sigma(at, m, 3)
            s, chosen, bad = m3.good_complement(B, 3)
            self.assertFalse(bad)
            Wb = [1 << i for i in chosen] + [1 << (c + j) for j in range(y)]
            for _ in range(3):
                v = m3.combine(sol, rng.getrandbits(len(sol))) if sol else 0
                S = m3.sigma_from_coeffs(v, tabs, 3)
                sv = m3.table(S, m)
                lc, ex = m3.least_codim(m3.zero_mask_of(S, m), m, xms[m])
                self.assertTrue(ex)
                if Wb:
                    lw, ex2 = m3.least_codim(m3.restricted_zero_mask(sv, Wb), len(Wb),
                                             xms[len(Wb)])
                    self.assertTrue(ex2)
                else:
                    lw = 0
                self.assertLessEqual(lc, lw)


if __name__ == "__main__":
    unittest.main()
