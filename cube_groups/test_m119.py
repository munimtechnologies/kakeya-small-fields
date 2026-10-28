# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m119.py (job m119, cube_groups/m119-predictions.md). Needs m42.py, sat_aniso.py,
m100.py to m106.py, m110.py to m112.py next to it. The case was read by hand from
results/m112l/m112l_skipped.json on 2026-10-28."""
import tempfile
import time
import unittest

import m119


class TestM119(unittest.TestCase):
    def test_case_is_d1(self):
        self.assertIn(m119.CASE, m119.m112.d1_cases())
        self.assertEqual(m119.CASE[20:], "t3_m012_032")

    def test_grade_without_rows(self):
        with tempfile.TemporaryDirectory() as d:
            out = m119.grade(d)
            self.assertFalse(out["graded"]["run_ran"])
            self.assertFalse(out["graded"]["all_accounted"])

    def test_deadline_skips_without_solving(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m119.m112.solve_sweep("not-a-case", 1.0, time.time() - 1, d))


if __name__ == "__main__":
    unittest.main()
