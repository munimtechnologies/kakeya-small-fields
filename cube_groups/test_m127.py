# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m127.py (job m127, cube_groups/m127-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j and m120m, m120n, m120p next to it. Expectations worked out
by hand:

- 8 shards of 2 cases each cover the 16 open cases in name order, without overlap.
- Synthetic grade files: a SKIPPED y2 (m120m), a VERIFIED y1 and a SKIPPED y0 (m120n), an UNKNOWN
  y3 and a NOT_VERIFIED y4 (m120p) give [y0, y2, y3]; verified() is {y1}; with one grade file
  missing, None.
- The real grade files give the 16 names below (m120m 3 SKIPPED, m120n 5 SKIPPED, m120p 7 SKIPPED
  and 1 UNKNOWN), every one a d = 1 case, all in sweep mode.
"""
import json
import os
import tempfile
import unittest

import m113
import m127

REAL = ["r3b_t8_B7_o009_c006_t2_m031", "r3b_t8_B7_o010_c000_t3_m004_034",
        "r3b_t8_B7_o010_c001_t2_m058", "r3b_t8_B7_o010_c002_t3_m011_017",
        "r3b_t8_B7_o010_c003_t2_m011", "r3b_t8_B7_o010_c004_t2_m012",
        "r3b_t8_B7_o010_c004_t2_m030", "r3b_t8_B7_o010_c005_t2_m031",
        "r3b_t8_B7_o010_c005_t2_m034", "r3b_t8_B7_o010_c005_t3_m012_032",
        "r3b_t8_B7_o010_c006_t3_m031_036", "r3b_t8_B7_o010_c007_t2_m012",
        "r3b_t8_B7_o010_c007_t2_m030", "r3b_t8_B7_o010_c008_t2_m034",
        "r3b_t8_B7_o010_c008_t2_m058", "r3b_t8_B7_o010_c008_t3_m011_017"]


class TestM127(unittest.TestCase):
    def test_shards(self):
        items = [[f"u{k:02d}", "sweep"] for k in range(16)]
        got = [m127.shard_list(s, items) for s in m127.SHARDS]
        self.assertTrue(all(len(x) == 2 for x in got))
        self.assertEqual([y for x in got for y in x], items)
        self.assertEqual(m127.shard_list("a", items), [["u00", "sweep"], ["u01", "sweep"]])
        self.assertEqual(m127.shard_list("h", items), [["u14", "sweep"], ["u15", "sweep"]])
        self.assertEqual(len(m127.SHARDS) * m127.PER_SHARD, m127.N_OPEN)

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = {"m120m": {"y2": ["SKIPPED", "sweep"]},
                    "m120n": {"y1": ["VERIFIED", "sweep"], "y0": ["SKIPPED", "sweep"]},
                    "m120p": {"y3": ["UNKNOWN", "sweep"], "y4": ["NOT_VERIFIED", "sweep"]}}
            for name, r in rows.items():
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"rows": r}, f)
            self.assertEqual(m127.cases(d), [["y0", "sweep"], ["y2", "sweep"], ["y3", "sweep"]])
            self.assertEqual(m127.verified(d), {"y1"})
            os.remove(os.path.join(d, "m120n_grade.json"))
            self.assertIsNone(m127.cases(d))

    def test_real_files(self):
        items = m127.cases()
        self.assertIsNotNone(items)
        self.assertEqual([x for x, _ in items], REAL)
        self.assertTrue(all(m == "sweep" for _, m in items))
        d1 = m113.d1_cases()
        self.assertTrue(all(x in d1 for x in REAL))
        self.assertFalse(set(REAL) & m127.verified())


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
