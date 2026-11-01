# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m129.py (job m129, cube_groups/m129-predictions.md). Needs m113.py, the modules it
imports and m128_count.json next to it. Expectations worked out by hand:

- 15 shards of 2 cases cover the 30 open cases without overlap; shard a takes items 0 and 15,
  shard o items 14 and 29.
- Extra shard p is exactly shard i's second case, r3b_t8_B7_o010_c001_t2_m011.
- Extra shard q is exactly shard n's second case, r3b_t8_B7_o010_c008_t2_m031, with a drat-trim
  limit of 25,000 s; every other shard keeps 7,200 s.
- The list is sorted, has no repeats, and equals m128's missing list; every name is a d = 1 case.
"""
import unittest

import m113
import m129


class TestM129(unittest.TestCase):
    def test_shards(self):
        items = [f"u{k:02d}" for k in range(30)]
        got = [m129.shard_list(s, items) for s in m129.SHARDS]
        self.assertTrue(all(len(x) == 2 for x in got))
        self.assertEqual(sorted(y for x in got for y in x), items)
        self.assertEqual(m129.shard_list("a", items), ["u00", "u15"])
        self.assertEqual(m129.shard_list("o", items), ["u14", "u29"])

    def test_extra(self):
        self.assertEqual(m129.shard_list("p", m129.OPEN), ["r3b_t8_B7_o010_c001_t2_m011"])
        self.assertEqual(m129.shard_list("i", m129.OPEN)[1], "r3b_t8_B7_o010_c001_t2_m011")
        self.assertEqual(m129.shard_list("q", m129.OPEN), ["r3b_t8_B7_o010_c008_t2_m031"])
        self.assertEqual(m129.shard_list("n", m129.OPEN)[1], "r3b_t8_B7_o010_c008_t2_m031")

    def test_caps(self):
        self.assertEqual(m129.drat_cap("q"), 25000)
        self.assertEqual(m129.drat_cap("p"), 7200)
        self.assertEqual(m129.drat_cap("a"), 7200)

    def test_list(self):
        self.assertEqual(len(m129.OPEN), m129.N_OPEN)
        self.assertEqual(len(set(m129.OPEN)), m129.N_OPEN)
        self.assertEqual(m129.OPEN, sorted(m129.OPEN))
        self.assertEqual(m129.m128_missing(), m129.OPEN)
        d1 = m113.d1_cases()
        self.assertTrue(all(x in d1 for x in m129.OPEN))


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
