# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m105.py (job m105, notes/a97.md). Needs m42.py, sat_aniso.py, m100.py, m101.py,
m102.py, m103.py, m104.py and python-sat next to it. Every expected value below was worked out by
hand."""
import unittest

import m100
import m104
import m105


class TestM105(unittest.TestCase):
    def test_shards(self):
        counts = {}
        for i in range(m105.SWEEP_TOTAL):
            counts[m105.shard_of(i)] = counts.get(m105.shard_of(i), 0) + 1
        # 1078 = 4 * 269 + 2
        self.assertEqual(counts, {"a": 270, "b": 270, "c": 269, "d": 269})

    def test_d2_table(self):
        self.assertEqual(len(m105.D2_LE4), 13)
        # job m104a: le4_by_d["2"] = 1115
        self.assertEqual(sum(m105.D2_LE4.values()), 1115)
        rest = sum(v for n, v in m105.D2_LE4.items() if n not in m105.DONE)
        self.assertEqual(rest, m105.SWEEP_TOTAL)
        self.assertEqual(sorted(s["name"] for s in m105.d2_specs()), sorted(m105.D2_LE4))

    def test_levels(self):
        spec = m100.spec_of(0, 0)
        self.assertEqual(m105.level_idx(spec, "out3"), [0, 1, 2, 3, 8, 9, 10])
        self.assertEqual(m105.level_idx(spec, "noN_out3"), [8, 9, 10])
        self.assertEqual(m105.level_idx(spec, "out2_h57"), [0, 1, 2, 3, 8, 10])
        self.assertEqual(m105.level_idx(spec, "in1_h1"), [0, 1, 2, 3, 4])
        self.assertEqual(m105.level_idx(spec, "in4"), [0, 1, 2, 3, 4, 5, 6, 7])
        for lv in m105.W_SIZES:
            idx = m105.level_idx(spec, lv)
            self.assertEqual(idx, sorted(set(idx)))
            # 2^(dim W) - 1 non-zero vectors
            self.assertEqual(len(m104.w_masks(idx)), (1 << len(idx)) - 1)
            self.assertEqual(m105.W_SIZES[lv], (1 << len(idx)) - 1)

    def test_items(self):
        self.assertEqual(m105.CORE_ITEMS, 1 + 6 * 11 + 4 * 2)
        self.assertEqual(len(m105.CORE_LEVELS), 11)
        self.assertNotIn("out3", m105.CORE_LEVELS)


if __name__ == "__main__":
    unittest.main()
