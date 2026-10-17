# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for rank_classes.py. Pure Python: no SAT solver is needed."""
import random
import unittest

import rank_classes as rc
import sat_aniso as sa


class TestPolynomials(unittest.TestCase):
    def test_irreducibles(self):
        irr = rc.irreducibles(4)
        # x, x + 1, x^2 + x + 1, x^3 + x + 1, x^3 + x^2 + 1, x^4 + x + 1, x^4 + x^3 + 1,
        # x^4 + x^3 + x^2 + x + 1
        self.assertEqual(irr, [0b10, 0b11, 0b111, 0b1011, 0b1101, 0b10011, 0b11001, 0b11111])

    def test_partitions(self):
        self.assertEqual(list(rc.partitions(4)), [(4,), (3, 1), (2, 2), (2, 1, 1), (1, 1, 1, 1)])


class TestClasses(unittest.TestCase):
    def test_counts(self):
        # q^n + ... classes of n x n matrices over F_q at q = 2; GL(n, 2) has 1, 3, 6, 14, 27.
        for n, total, singular in ((1, 2, 1), (2, 6, 3), (3, 14, 8), (4, 34, 20), (5, 74, 47)):
            cls = rc.classes(n)
            self.assertEqual(len(cls), total)
            self.assertEqual(sum(c["rank"] < n for c in cls), singular)
        self.assertEqual(rc.rank_counts(4), {0: 1, 1: 2, 2: 6, 3: 11, 4: 14})
        self.assertEqual(rc.rank_counts(5), {0: 1, 1: 2, 2: 6, 3: 13, 4: 25, 5: 27})
        self.assertEqual(rc.rank_counts(6)[3], 14)

    def test_rank_is_t_minus_parts_at_x(self):
        for n in range(1, 6):
            for c in rc.classes(n):
                parts = sum(len(lam) for p, lam in c["inv"] if p == rc.X_POLY)
                self.assertEqual(c["rank"], n - parts)

    def test_brute_force_orbits(self):
        for n in (1, 2, 3):
            st = rc.check_classes(n)
            self.assertTrue(st["agree"], st)

    def test_two_by_two(self):
        reps = sorted(c["C"] for c in rc.classes(2))
        # 0, diag(0, 1), E_21 (nilpotent), I, companion of (x + 1)^2, companion of x^2 + x + 1
        self.assertEqual(reps, sorted([0, sa.entries(2, [(1, 1)]), sa.entries(2, [(1, 0)]),
                                       sa.entries(2, [(0, 0), (1, 1)]),
                                       sa.entries(2, [(0, 1), (1, 0)]),
                                       sa.entries(2, [(1, 0), (0, 1), (1, 1)])]))


class TestCentraliser(unittest.TestCase):
    def test_against_brute_force(self):
        group = rc.gl(3)
        self.assertEqual(len(group), 168)
        for c in rc.classes(3):
            C = c["C"]
            brute = [g for g in group if sa.mat_mul(g, C, 3) == sa.mat_mul(C, g, 3)]
            self.assertEqual(sorted(rc.centraliser_units(C, 3)), sorted(brute))

    def test_kernel_reps(self):
        for c in rc.classes(3):
            C = c["C"]
            units = rc.centraliser_units(C, 3)
            ker = {x for x in range(1, 8) if sa.mat_apply(C, x, 3) == 0}
            reps = rc.kernel_reps(C, 3, units)
            orbits = [{sa.mat_apply(g, x, 3) for g in units} for x in reps]
            self.assertTrue(set(reps) <= ker)
            self.assertEqual(sum(len(o) for o in orbits), len(ker))
            self.assertEqual(set().union(*orbits) if orbits else set(), ker)

    def test_instances_t3(self):
        # Rank 2: one class with 1-dim kernel each, so one instance per class (5 classes).
        self.assertEqual(len(rc.instances(3, (2,))), rc.rank_counts(3)[2])
        self.assertEqual(rc.rank_counts(3), {0: 1, 1: 2, 2: 5, 3: 6})


class TestNormalisation(unittest.TestCase):
    def test_example1(self):
        As, ss, B = sa.example1()
        cls, group = rc.classes(3), rc.gl(3)
        k, s1, nAs, nss, nB = rc.normalised(As, ss, B, 3, cls, group)
        self.assertEqual(cls[k]["rank"], 1)
        self.assertEqual(nAs[0], cls[k]["C"])
        self.assertTrue(rc.accepts(cls[k]["C"], s1, nAs, nss, nB, 3, 2))
        bad = dict(nB)
        bad[(0, 1)] ^= 1
        self.assertFalse(rc.accepts(cls[k]["C"], s1, nAs, nss, bad, 3, 2))

    def test_random(self):
        st = rc.normalisation_check(random.Random(5), 40)
        self.assertEqual(st["disagree"], 0, st)
        self.assertTrue(0 < st["accepted"] < st["cases"], st)


if __name__ == "__main__":
    unittest.main()
