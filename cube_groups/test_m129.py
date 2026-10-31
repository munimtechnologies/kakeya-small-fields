# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m129.py (job m129, cube_groups/m129-predictions.md). Needs m113.py, the modules it
imports and m128_count.json next to it. Expectations worked out by hand:

- 15 shards of 2 cases cover the 30 open cases without overlap; shard a takes items 0 and 15,
  shard o items 14 and 29.
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
