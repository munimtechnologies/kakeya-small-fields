# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
import itertools
import random
import unittest

import nf_pencil as npc


class TestCounterexample(unittest.TestCase):
    def test_counterexample(self):
        ce = npc.check_counterexample()
        self.assertTrue(ce["identity"])
        self.assertTrue(ce["pencil_conditions"])
        self.assertTrue(ce["in_sol"])
        self.assertTrue(ce["anisotropic"])
        self.assertEqual(ce["least_codim"], 2)
        self.assertIsNone(ce["nf_bruteforce"])
        self.assertFalse(ce["criterion"])
        self.assertEqual(ce["fix_sum"], [0, 1])
        self.assertEqual(ce["singular"], [True, True, True])
        self.assertEqual(ce["sol_dims_y0_to_3"], [1, 1, 1, 1])
        self.assertEqual(ce["sol_inside_nf_y0_to_3"], [False] * 4)

    def test_counterexample_anisotropic_search(self):
        t, A1, A2, q1, q2, b = npc.counterexample()
        cnt, D, exh, ex = npc.anisotropic_in([A1, A2], 0, t, {})
        self.assertEqual((cnt, D, exh), (1, 1, True))
        levels, fin = npc.singular_subspaces(3, 2)
        self.assertTrue(fin)
        self.assertEqual(len(levels[1]), 343)
        self.assertIn(tuple(sorted((0, A1, A2, A1 ^ A2))), set(levels[2]))


class TestPencils(unittest.TestCase):
    def test_invertible_count(self):
        self.assertEqual(sum(not npc.is_singular(A, 2) for A in range(16)), 6)
        self.assertEqual(sum(not npc.is_singular(A, 3) for A in range(512)), 168)

    def test_pencil_conditions_match_identity(self):
        rng = random.Random(1)
        t, A1, A2, _, _, _ = npc.counterexample()
        cases = [(2, P) for P in npc.all_pencils(2)]
        cases += [(3, P) for P in npc.random_pencils(3, 5, rng)] + [(3, (A1, A2))]
        for t, (B1, B2) in cases:
            at = npc.pencil_alpha(B1, B2)
            sysset = set(npc.pencil_systems(B1, B2, t))
            for trip in itertools.product(range(1 << t), repeat=3):
                ok = npc.identity_holds_table(at, npc.pencil_sigma(*trip), 2, t)
                self.assertEqual(ok, trip in sysset)

    def test_t2_every_pencil_in_normal_form(self):
        n = 0
        for A1, A2 in npc.all_pencils(2):
            n += 1
            at = npc.pencil_alpha(A1, A2)
            for q1, q2, b in npc.pencil_systems(A1, A2, 2):
                self.assertTrue(npc.pencil_criterion(A1, A2, b, 2))
                self.assertIsNotNone(npc.nf_bruteforce(at, npc.pencil_sigma(q1, q2, b), 2, 2))
        self.assertEqual(n, 35)

    def test_criterion_matches_bruteforce_t3(self):
        rng = random.Random(2)
        t, A1, A2, _, _, _ = npc.counterexample()
        pencils = list(npc.random_pencils(3, 40, rng)) + [(A1, A2)]
        for B1, B2 in pencils:
            at = npc.pencil_alpha(B1, B2)
            for q1, q2, b in npc.pencil_systems(B1, B2, 3):
                brute = npc.nf_bruteforce(at, npc.pencil_sigma(q1, q2, b), 2, 3)
                self.assertEqual(brute is not None, npc.pencil_criterion(B1, B2, b, 3))

    def test_invertible_element_gives_normal_form(self):
        rng = random.Random(3)
        seen = 0
        for B1, B2 in npc.random_pencils(3, 200, rng):
            if not npc.has_invertible(B1, B2, 3):
                continue
            seen += 1
            for q1, q2, b in npc.pencil_systems(B1, B2, 3):
                self.assertTrue(npc.pencil_criterion(B1, B2, b, 3))
        self.assertGreater(seen, 50)


class TestRank3(unittest.TestCase):
    def test_f_criterion_t2_rank3(self):
        rng = random.Random(4)
        tabs = npc.mon_tables(3)
        for B in npc.subspaces(4, 3):
            m, at = npc.system(B, 0)
            sol = npc.solve_sigma(at, m, 2)
            D = len(sol)
            if D == 0:
                continue
            picks = range(1, 1 << D) if D <= 4 else [rng.randrange(1, 1 << D) for _ in range(16)]
            for p in picks:
                sv = npc.table(npc.sigma_from_coeffs(npc.combine(sol, p), tabs, 2), m)
                self.assertTrue(npc.identity_holds_table(at, sv, m, 2))
                brute = npc.nf_bruteforce(at, sv, m, 2)
                self.assertEqual(brute is not None, npc.f_criterion(B, sv, 2))


class TestAnisotropic(unittest.TestCase):
    def test_singular_levels_t2(self):
        levels, fin = npc.singular_subspaces(2, 3)
        self.assertTrue(fin)
        self.assertEqual({c: len(v) for c, v in levels.items()}, {0: 1, 1: 9, 2: 6, 3: 0})

    def test_small_t(self):
        tabs = {}
        lv1, _ = npc.singular_subspaces(1, 2)
        self.assertGreater(npc.aniso_search(1, 1, lv1, tabs)["systems_with_anisotropic"], 0)
        st = npc.aniso_search(1, 2, lv1, tabs)
        self.assertTrue(st["finished"])
        self.assertEqual(st["anisotropic_sigmas"], 0)
        lv2, _ = npc.singular_subspaces(2, 3)
        self.assertGreater(npc.aniso_search(2, 2, lv2, tabs)["systems_with_anisotropic"], 0)
        st = npc.aniso_search(2, 3, lv2, tabs)
        self.assertTrue(st["finished"])
        self.assertEqual(st["anisotropic_sigmas"], 0)


if __name__ == "__main__":
    unittest.main()
