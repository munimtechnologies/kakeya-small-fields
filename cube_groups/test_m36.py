# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m36.py (pure Python; no SAT solver)."""
import unittest

import m32
import m36
import sat_aniso as sa


class TestTargets(unittest.TestCase):
    def test_groups(self):
        names = [n for g in m36.GROUPS.values() for n in g]
        self.assertEqual(len(names), 4)
        self.assertEqual(len(set(names)), 4)
        self.assertTrue(all(n in m32.B5_UNKNOWN for n in names))
        self.assertEqual({m32.orbit_of(n) for n in m36.GROUPS["m36"]}, {2})
        self.assertEqual({m32.orbit_of(n) for n in m36.GROUPS["m37"]}, {4})

    def test_matrices(self):
        """Hand values (entry (row, col) at bit 6 row + col): o002 m000 = 2164736, bits 11, 16, 21,
        entries (1, 5), (2, 4), (3, 3), image span(e_1, e_2, e_3); o004 m001 = 4229136, bits 4, 11,
        15, 22, entries (0, 4), (1, 5), (2, 3), (3, 4), image span(e_0 + e_3, e_1, e_2)."""
        self.assertEqual(m32.EXPECTED_AU["r3m_t6_r3_B5_o002_m000"], (1 << 11) + (1 << 16) + (1 << 21))
        self.assertEqual(m32.EXPECTED_AU["r3m_t6_r3_B5_o004_m001"],
                         (1 << 4) + (1 << 11) + (1 << 15) + (1 << 22))
        self.assertEqual(sorted(sa.mat_apply(m32.EXPECTED_AU["r3m_t6_r3_B5_o004_m001"], 1 << c, 6)
                                for c in (3, 4, 5)), [2, 4, 9])
        for g in m36.GROUPS.values():
            for n in g:
                au = m32.EXPECTED_AU[n]
                self.assertEqual(sa.rank_f2(sa.rows_of(au, 6)), 3, n)
                for x in (1, 2, 4):             # X_1 = span(e_0, e_1, e_2)
                    self.assertEqual(sa.mat_apply(au, x, 6), 0, n)


class TestShare(unittest.TestCase):
    def test_share(self):
        self.assertEqual(m36.share(148 * 60, 2), 74 * 60)
        self.assertEqual(m36.share(100.0, 1), 100.0)
        self.assertEqual(m36.share(100.0, 0), 0.0)

    def test_floor(self):
        """Even if nothing is left over, each instance gets at least the rule's 40 minutes."""
        self.assertGreaterEqual(m36.share(148 * 60, 2), m36.MIN_SECONDS)


if __name__ == "__main__":
    unittest.main()
