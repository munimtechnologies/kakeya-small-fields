# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m116.py (job m116, cube_groups/m116-predictions.md). Needs m42.py, sat_aniso.py,
m100.py to m106.py, m110.py to m112.py next to it. The 14 skipped cases were read by hand from the
grade files of m112i (6), m112j (7) and m112k (1) on 2026-10-27."""
import tempfile
import time
import unittest

import m100
import m116


class TestM116(unittest.TestCase):
    def test_cases(self):
        self.assertEqual(len(m116.SKIPPED), 14)
        self.assertEqual(len(set(m116.SKIPPED)), 14)
        cases = m116.m112.d1_cases()
        self.assertTrue(all(x in cases for x in m116.SKIPPED))
        a, b = (m116.shard_list(s, m116.SKIPPED) for s in "ab")
        self.assertEqual((len(a), len(b)), (7, 7))
        self.assertEqual(sorted(a + b), m116.SKIPPED)

    def test_skipped_of(self):
        m = {"i": {"skipped": ["x1_sweep", "x0_sweep"]}, "j": {"skipped": []},
             "k": {"skipped": ["y_sweep"]}}
        self.assertEqual(m116.skipped_of(m), ["x0", "x1", "y"])
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m116.sources(d))
            for s in "ijk":
                m100_save(d, f"m112{s}_grade.json", m[s])
            self.assertEqual(m116.skipped_of(m116.sources(d)), ["x0", "x1", "y"])

    def test_deadline_skips_without_solving(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m116.m112.solve_sweep("not-a-case", 1.0, time.time() - 1, d))


def m100_save(d, name, obj):
    m116.save(d, name, obj)
    assert m100.load(d, name) == obj


if __name__ == "__main__":
    unittest.main()
