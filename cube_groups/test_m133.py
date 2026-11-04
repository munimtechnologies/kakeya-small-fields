# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m133.py (job m133, cube_groups/m133-predictions.md). Needs m100, m102, m105,
m113, m130 and m132 next to it. Expectations worked out by hand:

- m132 certified 100 distinct cases (28 + 33 + 39), all among the 1,494 uncertified after m131;
  1,494 - 100 = 1,394 remain;
- 1,394 = 48 * 29 + 2, so shards 0 and 1 hold 30 cases and shards 2 .. 47 hold 29; the 48 shards
  are disjoint and cover the census; on a toy list shard k is names[k], names[k + 48], ...;
- the caps are m132's, and the last case can start no later than 25,000 s, which leaves
  1,500 + 4,000 s plus setup inside 540 minutes.
"""
import unittest

import m130
import m132
import m133


class TestM133(unittest.TestCase):
    def test_done(self):
        d = m133.done_names()
        self.assertEqual(len(d), 100)
        self.assertTrue(set(d) <= set(m132.remaining()))
        self.assertFalse(set(d) & m132.pilot())

    def test_census_and_shards(self):
        cen = m133.census()
        self.assertEqual(len(cen), 1394)
        self.assertEqual(len(set(cen)), 1394)
        shards = [m133.shard_cases(k) for k in range(m133.NSH)]
        self.assertEqual([len(x) for x in shards[:3]], [30, 30, 29])
        self.assertTrue(all(len(x) == 29 for x in shards[2:]))
        self.assertEqual(sorted(sum(shards, [])), sorted(cen))
        table = m130.by_name()
        for x in shards[0]:
            self.assertEqual(table[x][0]["dmeet"], 0)

    def test_toy(self):
        names = [f"n{k:04d}" for k in range(1394)]
        s = m133.shard_cases(5, names)
        self.assertEqual(s[:3], ["n0005", "n0053", "n0101"])
        self.assertEqual(len(s), 29)
        self.assertEqual(m133.census(names[:10], ["n0003"]), [x for x in names[:10] if x != "n0003"])

    def test_caps(self):
        self.assertEqual(m133.MODE, "sweep")
        self.assertEqual(m133.CADICAL_CAP, 1500.0)
        self.assertEqual(m133.DRAT_CAP["sweep"], 4000)
        self.assertLess(m133.NO_START_AFTER + m133.CADICAL_CAP + m133.DRAT_CAP["sweep"] + 600,
                        540 * 60)
        self.assertEqual(m133.fname(3, "cert"), "m133s03_cert.json")


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
