# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for a6_r3.py (job m27). Pure Python; the expected values are worked out by hand in
m27/predictions.md."""
import json
import os
import tempfile
import unittest

import a6_r3 as r3
import sat_aniso as sa

# Lemma 63 (ii) at t = 2 with e = e_0, f = e_1: sigma(a) = sigma(b) = e_0, beta(a, b) = e_1,
# A_a = A_b = p, p e_0 = 0, p e_1 = e_1, so p has its one entry at (1, 1), bit 2 * 1 + 1 = 3.
P_E1 = 8
KIND_II_B = ([P_E1, P_E1], [1, 1], {(0, 1): 2})        # u = a, h_1 = b: shape ("B", 1)
# The same system with e = e_1, f = e_0 (p now has its entry at (0, 0)), u = a + b, h_1 = a:
# sigma(u) = f = e_0, beta(u, a) = f = e_0, A_u = 0: shape ("A", 1).
KIND_II_A = ([0, 1], [1, 2], {(0, 1): 1})


def accepts(system, t, d, shape, p, x1, r):
    As, ss, B = system
    cnf, names = r3.encode_r3(t, d, shape, p, x1, r)
    return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, t, d))


class TestSubspaces(unittest.TestCase):
    def test_rref(self):
        self.assertEqual(r3.rref([3, 1]), (2, 1))
        self.assertEqual(r3.rref([1, 2]), (2, 1))
        self.assertEqual(r3.rref([5, 6, 3]), (5, 3))      # 5 + 6 = 3, so a plane
        self.assertEqual(r3.rref([0, 4]), (4,))

    def test_counts(self):
        self.assertEqual(len(r3.subspaces(4, 2)), 35)
        self.assertEqual(len(r3.subspaces(4, 2, 1)), 7)
        self.assertEqual(r3.subspaces(2, 1), [(1,), (2,), (3,)])
        self.assertEqual(r3.dim_meet((2, 1), (3,)), 1)


class TestGroup(unittest.TestCase):
    def test_orders(self):
        for (t, s, p), n in r3.HAND_GROUP.items():
            self.assertEqual(r3.group_order(t, s, p), n, (t, s, p))

    def test_generators(self):
        for t, s, p in [(2, "A", 1), (2, "B", 1), (4, "A", 3), (4, "B", 3), (4, "B", 2),
                        (6, "A", 5), (6, "B", 4), (6, "B", 5)]:
            self.assertTrue(all(r3.in_group(g, t, s, p) for g in r3.generators(t, s, p)))
        self.assertEqual(len(r3.generators(2, "A", 1)), 1)
        self.assertEqual(len(r3.generators(2, "B", 1)), 0)
        self.assertEqual(len(r3.generators(6, "A", 5)), 21)
        self.assertFalse(r3.in_group(sa.from_cols([1, 1 | 2], 2), 2, "B", 1))

    def test_orbits_small(self):
        self.assertEqual(sorted(o[2] for o in r3.orbits(2, "A", 1, 1)), [1, 2])
        self.assertEqual(len(r3.orbits(2, "B", 1, 1)), 3)
        b3 = r3.orbits(4, "B", 3, 2)
        self.assertEqual(sorted(o[2] for o in b3), r3.HAND_ORBITS[(4, "B", 3)])
        self.assertEqual(sum(o[2] for o in r3.orbits(4, "A", 3, 2)), 245)
        self.assertTrue(all(r3.group_order(4, "A", 3) % o[2] == 0
                            for o in r3.orbits(4, "A", 3, 2)))
        ds = [r3.dim_meet(o[0], o[1]) for o in b3]
        self.assertEqual(ds, sorted(ds, reverse=True))


class TestEncoding(unittest.TestCase):
    def test_hand_systems(self):
        for As, ss, B in (KIND_II_A, KIND_II_B):
            at, sv = sa.tables(As, ss, B, 2)
            self.assertTrue(sa.is_system(at, sv, 2, 2))
            self.assertTrue(sa.anisotropic(sv))

    def test_kind_ii_b(self):
        self.assertTrue(accepts(KIND_II_B, 2, 2, "B", 1, (1,), (2,)))
        self.assertFalse(accepts(KIND_II_B, 2, 2, "B", 1, (1,), (1,)))
        self.assertFalse(accepts(KIND_II_B, 2, 2, "B", 1, (1,), (3,)))
        self.assertFalse(accepts(KIND_II_B, 2, 2, "A", 1, (1,), (2,)))
        self.assertTrue(r3.in_normal_form(*KIND_II_B, 2, 2, "B", 1, (1,), (2,)))
        self.assertFalse(r3.in_normal_form(*KIND_II_B, 2, 2, "B", 1, (1,), (3,)))

    def test_kind_ii_a(self):
        for r in ((1,), (2,), (3,)):
            self.assertTrue(accepts(KIND_II_A, 2, 2, "A", 1, (1,), r))
        self.assertFalse(accepts(KIND_II_A, 2, 2, "B", 1, (1,), (2,)))

    def test_wanted_phi(self):
        self.assertEqual([r3.wanted_phi(i, 7, "A", 5) for i in range(1, 7)], [0, 1, 2, 4, 8, 16])
        self.assertEqual([r3.wanted_phi(i, 7, "B", 4) for i in range(1, 7)], [0, 0, 2, 4, 8, 16])
        self.assertEqual([r3.wanted_phi(i, 7, "B", 5) for i in range(1, 7)], [0, 2, 4, 8, 16, 32])


class TestGrade(unittest.TestCase):
    def test_expected(self):
        self.assertEqual(r3.expected_control(2, "A", [1]), "SAT")
        self.assertEqual(r3.expected_control(2, "B", [2]), "SAT")
        self.assertEqual(r3.expected_control(2, "B", [3]), "UNSAT")
        self.assertEqual(r3.expected_control(4, "A", [2, 1]), "UNSAT")

    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = [{"name": "r3_t2_B1_o000", "t": 2, "shape": "B", "p": 1, "r": [2],
                     "status": "SAT", "verified": True},
                    {"name": "r3_t2_B1_o001", "t": 2, "shape": "B", "p": 1, "r": [1],
                     "status": "UNSAT"},
                    {"name": "r3_t6_A5_o000", "t": 6, "shape": "A", "p": 5, "r": [4, 2, 1],
                     "status": "UNSAT"},
                    {"name": "r3_t6_A5_o001", "t": 6, "shape": "A", "p": 5, "r": [4, 2, 1],
                     "status": "UNKNOWN"}]
            for row in rows:
                with open(os.path.join(d, row["name"] + ".json"), "w") as f:
                    json.dump(row, f)
            with open(os.path.join(d, "r3_t6_A5_o000.spec.json"), "w") as f:
                json.dump({"junk": 1}, f)
            g = r3.grade(d)
            self.assertEqual(g["ungraded"], {"selfcheck": "missing"})
            self.assertTrue(all(g["graded"].values()))
            self.assertEqual(g["per_shape"]["A5"]["counts"], {"UNKNOWN": 1, "UNSAT": 1})
            self.assertEqual(g["per_shape"]["A5"]["undecided"], ["r3_t6_A5_o001"])
            self.assertFalse(g["per_shape"]["A5"]["all_unsat"])
            self.assertEqual(g["per_shape"]["B4"]["instances"], 0)
            self.assertFalse(g["any_sat_6"])


if __name__ == "__main__":
    unittest.main()
