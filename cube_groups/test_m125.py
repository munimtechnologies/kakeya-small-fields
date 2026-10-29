# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m125.py (job m125, cube_groups/m125-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j, m120a, m120h-l, m122a and m123a-b next to it. Expectations
worked out by hand:

- 42 = 3 * 14: positions 0, 3, 6, ... go to shard a, 1, 4, ... to b, 2, 5, ... to c, 14 each; the
  last name (x041) is in c. Shard d is the UNKNOWN list, 4 names.
- Synthetic grade files: SKIPPED rows x1 (m120a) and x3 (m120l), a VERIFIED x2 (m120h), an UNKNOWN
  x4 (m120k, which is a source of both lists) and an UNKNOWN x5 (m123b) give SKIPPED [x1, x3] and
  UNKNOWN [x4, x5]; with one grade file missing, None.
- The real grade files load and every case they give is a d = 1 case. The counts (42 and 4) are
  graded in the check part.
"""
import json
import os
import tempfile
import unittest

import m113
import m125


class TestM125(unittest.TestCase):
    def test_sizes(self):
        skipped = [f"x{i:03d}" for i in range(m125.N_SKIPPED)]
        unknown = [f"u{i}" for i in range(m125.N_UNKNOWN)]
        for s in m125.SIZE:
            self.assertEqual(len(m125.shard_list(s, skipped, unknown)), m125.SIZE[s], s)
        self.assertEqual(m125.shard_list("c", skipped, unknown)[-1], ["x041", "sweep"])
        self.assertEqual(m125.shard_list("d", skipped, unknown)[0], ["u0", "sweep"])
        self.assertEqual(sum(m125.SIZE.values()), m125.N_SKIPPED + m125.N_UNKNOWN)

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = {name: {} for name in set(m125.SOURCES_SKIPPED) | set(m125.SOURCES_UNKNOWN)}
            rows["m120a"]["x1"] = ["SKIPPED"]
            rows["m120h"]["x2"] = ["VERIFIED", "sweep"]
            rows["m120l"]["x3"] = ["SKIPPED"]
            rows["m120k"]["x4"] = ["UNKNOWN", "sweep"]
            rows["m123b"]["x5"] = ["UNKNOWN", "sweep"]
            for name, r in rows.items():
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"rows": r}, f)
            self.assertEqual(m125.cases(d), (["x1", "x3"], ["x4", "x5"]))
            os.remove(os.path.join(d, "m122a_grade.json"))
            self.assertIsNone(m125.cases(d))

    def test_real_files_load(self):
        # the counts themselves are graded checks of the check part, not test failures
        both = m125.cases()
        self.assertIsNotNone(both)
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in both[0] + both[1]))


if __name__ == "__main__":
    unittest.main()
