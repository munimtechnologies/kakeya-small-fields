# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m123.py (job m123, cube_groups/m123-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j and m120e-g next to it. Expectations worked out by hand:

- 30 = 2 * 15: even positions go to shard a, odd to b, 15 each; the last name (x029) is in b.
- Synthetic grade files: m120e rows x1 SKIPPED and x2 VERIFIED, m120f x3 SKIPPED, m120g x4 NOT_VERIFIED
  and x5 SKIPPED give the cases [x1, x3, x5] (only SKIPPED rows); with one grade file missing, None.
- The real grade files load and every case they give is a d = 1 case. The counts (30 and 48) are
  graded in the check part.
"""
import json
import os
import tempfile
import unittest

import m113
import m123


class TestM123(unittest.TestCase):
    def test_sizes(self):
        self.assertEqual(sum(m123.SIZE.values()), m123.TOTAL)
        names = [f"x{i:03d}" for i in range(m123.TOTAL)]
        for s in m123.SHARDS:
            self.assertEqual(len(m123.shard_list(s, names)), m123.SIZE[s], s)
        self.assertEqual(m123.shard_list("b", names)[-1], ["x029", "sweep"])

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = {"m120e": {"x1": ["SKIPPED"], "x2": ["VERIFIED", "sweep"]},
                    "m120f": {"x3": ["SKIPPED"]},
                    "m120g": {"x4": ["NOT_VERIFIED", "sweep"], "x5": ["SKIPPED"]}}
            for name, r in rows.items():
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"rows": r}, f)
            self.assertEqual(m123.cases(d), ["x1", "x3", "x5"])
            os.remove(os.path.join(d, "m120g_grade.json"))
            self.assertIsNone(m123.cases(d))

    def test_real_files_load(self):
        # the counts themselves are graded checks of the check part, not test failures
        names = m123.cases()
        self.assertIsNotNone(names)
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in names))


if __name__ == "__main__":
    unittest.main()
