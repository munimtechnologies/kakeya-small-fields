# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m120.py (job m120, cube_groups/m120-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j, m112a-l, m114a-f, m116a-b, m117 and m119 next to it.
Expectations worked out by hand:

- 435 = 16 * 27 + 3: positions 432, 433, 434 fall to shards a, b, c (432 = 16 * 27), so a-c hold
  28 cases and d-p 27; together 435.
- The real grade files load and every case they give is a d = 1 case. The counts (notes/a108.md and
  a109.md: 3,846 UNSAT answers, 3,408 decided by m110a-j, so 438 by the sweep alone, less m117's
  three VERIFIED = 435) are graded in the check part.
- Synthetic grade files: UNSAT {x1, x2} in m112a and {x2, x3} in m114a, m117 VERIFIED x1 (x3
  UNKNOWN) gives the cases [x2, x3]; with one sweep grade file missing, None.
"""
import json
import os
import tempfile
import unittest

import m113
import m120


class TestM120(unittest.TestCase):
    def test_sizes(self):
        self.assertEqual(sum(m120.SIZE.values()), m120.TOTAL)
        names = [f"x{i:03d}" for i in range(m120.TOTAL)]
        for s in m120.SHARDS:
            self.assertEqual(len(m120.shard_list(s, names)), m120.SIZE[s], s)
        self.assertEqual(m120.shard_list("c", names)[-1], ["x434", "sweep"])

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            for name in m120.SWEEP_SOURCES:
                unsat = {"m112a": ["x1", "x2"], "m114a": ["x2", "x3"]}.get(name, [])
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"unsat": unsat}, f)
            with open(os.path.join(d, "m117_grade.json"), "w") as f:
                json.dump({"rows": {"x1": ["VERIFIED", 1.0], "x3": ["UNKNOWN", 2.0]}}, f)
            self.assertEqual(m120.cases(d), ["x2", "x3"])
            os.remove(os.path.join(d, "m119_grade.json"))
            self.assertIsNone(m120.cases(d))

    def test_real_files_load(self):
        # the counts themselves are graded checks of the check part, not test failures
        names = m120.cases()
        self.assertIsNotNone(names)
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in names))


if __name__ == "__main__":
    unittest.main()
