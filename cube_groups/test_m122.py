# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m122.py (job m122, cube_groups/m122-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j, m111b-c and m120b-d next to it. Expectations worked out by
hand:

- 53 = 3 * 17 + 2: positions 51 and 52 fall to shards a and b (51 = 3 * 17), so a and b hold 18
  cases and c 17; together 53, and the last name (x052) is in shard b.
- Synthetic grade files: m111b decided {x1}, m111c {x2}; m120b rows x3 SKIPPED and x4 VERIFIED,
  m120c x2 SKIPPED, m120d x5 SKIPPED gives the cases [x1, x2, x3, x5] (x4 is certified, x2 counted
  once); with one m120 grade file missing, None.
- The real grade files load and every case they give is a d = 1 case. The counts (15 and 38) are
  graded in the check part.
"""
import json
import os
import tempfile
import unittest

import m113
import m122


class TestM122(unittest.TestCase):
    def test_sizes(self):
        self.assertEqual(sum(m122.SIZE.values()), m122.TOTAL)
        names = [f"x{i:03d}" for i in range(m122.TOTAL)]
        for s in m122.SHARDS:
            self.assertEqual(len(m122.shard_list(s, names)), m122.SIZE[s], s)
        self.assertEqual(m122.shard_list("b", names)[-1], ["x052", "sweep"])

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            for name, dec in (("m111b", ["x1"]), ("m111c", ["x2"])):
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"decided": dec}, f)
            rows = {"m120b": {"x3": ["SKIPPED"], "x4": ["VERIFIED", "sweep"]},
                    "m120c": {"x2": ["SKIPPED"]}, "m120d": {"x5": ["SKIPPED"]}}
            for name, r in rows.items():
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"rows": r}, f)
            self.assertEqual(m122.cases(d), ["x1", "x2", "x3", "x5"])
            os.remove(os.path.join(d, "m120d_grade.json"))
            self.assertIsNone(m122.cases(d))

    def test_real_files_load(self):
        # the counts themselves are graded checks of the check part, not test failures
        names = m122.cases()
        self.assertIsNotNone(names)
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in names))


if __name__ == "__main__":
    unittest.main()
