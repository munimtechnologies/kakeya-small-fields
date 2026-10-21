# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m32.py (pure Python; no SAT solver)."""
import unittest

import a6_r3m as m
import m32
import sat_aniso as sa


class TestControl(unittest.TestCase):
    def test_diag_construction(self):
        c = m32.control_checks(False)
        for k, v in c.items():
            self.assertTrue(v, k)

    def test_skew_construction(self):
        c = m32.control_checks(True)
        self.assertFalse(c.pop("symmetric"))
        for k, v in c.items():
            self.assertTrue(v, k)

    def test_hand_values(self):
        self.assertEqual(m32.HAND_CONTROL[False]["au"], (1 << 7) + (1 << 14) + (1 << 21))
        self.assertEqual(m32.HAND_CONTROL[True]["au"], (1 << 7) + (1 << 14) + (1 << 21) + (1 << 10))

    def test_transpose_breaks_kernel(self):
        As, ss, B, x1, r, au = m32.direct_sum_control(True)
        at = m32.transpose(au, 6)
        self.assertEqual(m32.transpose(at, 6), au)
        self.assertNotEqual(m.ker_of(at, 6), x1)

    def test_control_specs(self):
        sps = m32.control_specs()
        self.assertEqual([sp["name"] for sp in sps], ["ctl6_diag", "ctl6_skew", "ctl6_skew_transposed"])
        self.assertEqual([sp["expect"] for sp in sps], ["SAT", "SAT", "UNSAT"])
        self.assertTrue(all(sp["d"] == 6 and sp["shape"] == "B" and sp["p"] == 3 for sp in sps))


class TestTargets(unittest.TestCase):
    def test_counts(self):
        self.assertEqual((len(m32.B4_LEFT), len(m32.B5_SKIPPED), len(m32.B5_UNKNOWN)), (2, 24, 25))
        self.assertEqual({k: len(v) for k, v in m32.GROUPS.items()}, {"m32": 26, "m33": 11, "m34": 14})

    def test_groups_cover_once(self):
        names = [n for g in m32.GROUPS.values() for n, _ in g]
        self.assertEqual(len(names), len(set(names)))
        self.assertEqual(set(names), set(m32.EXPECTED_AU))

    def test_budgets(self):
        total = {k: sum(mins for _, mins in v) for k, v in m32.GROUPS.items()}
        self.assertEqual(total, {"m32": 112, "m33": 132, "m34": 140})
        self.assertTrue(m32.GROUPS["m32"][0][0].startswith("r3m_t6_r3_B4_"))

    def test_matrices_look_right(self):
        """Every transcribed A_u has rank 3 and kills e_0 (x0 = e_0 is in ker A_u)."""
        for name, au in m32.EXPECTED_AU.items():
            self.assertEqual(sa.rank_f2(sa.rows_of(au, 6)), 3, name)
            self.assertEqual(sa.mat_apply(au, 1, 6), 0, name)

    def test_orbit_of(self):
        self.assertEqual(m32.orbit_of("r3m_t6_r3_B5_o007_m003"), 7)


if __name__ == "__main__":
    unittest.main()
