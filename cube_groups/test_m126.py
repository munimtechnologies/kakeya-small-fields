# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m126.py (job m126, cube_groups/m126-predictions.md). Needs m113.py, the modules it
imports and the grade files of m110a-j and m125b-d next to it. Expectations worked out by hand:

- Shards a, b, c take the UNKNOWN names in sorted order, shard d the DRAT_STOPPED name; each shard
  is exactly one case.
- Synthetic grade files: an UNKNOWN y2 (m125b), a VERIFIED y1 and an UNKNOWN y3 (m125c), a
  DRAT_STOPPED y0 and an UNKNOWN y9 (m125d, where UNKNOWN is not a source status) give UNKNOWN
  [y2, y3] and DRAT_STOPPED [y0]; verified() is {y1}; with one grade file missing, None.
- The real grade files give r3b_t8_B7_o010_c004_t2_m031, ..._c006_t3_m011_017, ..._c007_t2_m031 and
  r3b_t8_B7_o010_c000_t2_m011, every one a d = 1 case.
"""
import json
import os
import tempfile
import unittest

import m113
import m126

REAL_UNKNOWN = ["r3b_t8_B7_o010_c004_t2_m031", "r3b_t8_B7_o010_c006_t3_m011_017",
                "r3b_t8_B7_o010_c007_t2_m031"]
REAL_STOPPED = ["r3b_t8_B7_o010_c000_t2_m011"]


class TestM126(unittest.TestCase):
    def test_shards(self):
        unknown, stopped = ["u0", "u1", "u2"], ["s0"]
        self.assertEqual(m126.shard_list("a", unknown, stopped), [["u0", "sweep"]])
        self.assertEqual(m126.shard_list("c", unknown, stopped), [["u2", "sweep"]])
        self.assertEqual(m126.shard_list("d", unknown, stopped), [["s0", "sweep"]])
        self.assertEqual(m126.shard_list("d", unknown, []), [])
        self.assertEqual(len(m126.SHARDS), m126.N_UNKNOWN + m126.N_STOPPED)
        self.assertEqual(set(m126.CADICAL_CAP), set(m126.SHARDS))
        self.assertEqual(set(m126.DRAT_CAP), set(m126.SHARDS))

    def test_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            rows = {"m125b": {"y2": ["UNKNOWN", "sweep"]},
                    "m125c": {"y1": ["VERIFIED", "sweep"], "y3": ["UNKNOWN", "sweep"]},
                    "m125d": {"y0": ["DRAT_STOPPED", "sweep"], "y9": ["UNKNOWN", "sweep"]}}
            for name, r in rows.items():
                with open(os.path.join(d, f"{name}_grade.json"), "w") as f:
                    json.dump({"rows": r}, f)
            self.assertEqual(m126.cases(d), (["y2", "y3"], ["y0"]))
            self.assertEqual(m126.verified(d), {"y1"})
            os.remove(os.path.join(d, "m125c_grade.json"))
            self.assertIsNone(m126.cases(d))

    def test_real_files(self):
        both = m126.cases()
        self.assertIsNotNone(both)
        self.assertEqual(both, (REAL_UNKNOWN, REAL_STOPPED))
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in both[0] + both[1]))


if __name__ == "__main__":
    unittest.main()
