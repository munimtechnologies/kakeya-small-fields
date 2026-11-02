# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m132.py (job m132, cube_groups/m132-predictions.md). Needs m100, m102, m105,
m113 and m130 next to it. Expectations worked out by hand:

- m130's six pilot cases include m131's three; 1,494 cases remain;
- the sample is 120 distinct names spread evenly over the remaining list, none a pilot case, all
  of classes with dmeet = 0; the three shards split it 40 / 40 / 40 with no overlap;
- on a toy list of 1,494 names the sample indices are floor(k * 1494 / 120) (0, 12, 24, 37, ...);
- the caps are CaDiCaL 1,500 s and drat-trim 4,000 s at the sweep CNF, and the last case can
  start no later than 25,000 s, which leaves 1,500 + 4,000 s plus setup inside 540 minutes;
- is_solution accepts only a SAT row whose model passes every m106 check.
"""
import unittest

import m130
import m132


class TestM132(unittest.TestCase):
    def test_pilot_and_sample(self):
        p = m132.pilot()
        self.assertEqual(len(p), 6)
        self.assertTrue(set(m132.M131_CASES) <= p)
        rem = m132.remaining()
        self.assertEqual(len(rem), 1494)
        s = m132.sample()
        self.assertEqual(len(set(s)), 120)
        self.assertFalse(set(s) & p)
        table = m130.by_name()
        for x in s:
            self.assertEqual(table[x][0]["dmeet"], 0)
        shards = [m132.shard_cases(sh) for sh in m132.SHARDS]
        self.assertEqual([len(x) for x in shards], [40, 40, 40])
        self.assertEqual(sorted(sum(shards, [])), sorted(s))

    def test_toy_indices(self):
        names = [f"n{k:04d}" for k in range(1494)]
        s = m132.sample(names)
        self.assertEqual(s[:4], ["n0000", "n0012", "n0024", "n0037"])
        self.assertEqual(s[-1], names[(119 * 1494) // 120])

    def test_caps(self):
        self.assertEqual(m132.MODE, "sweep")
        self.assertEqual(m132.CADICAL_CAP, 1500.0)
        self.assertEqual(m132.DRAT_CAP["sweep"], 4000)
        self.assertLess(m132.NO_START_AFTER + m132.CADICAL_CAP + m132.DRAT_CAP["sweep"] + 600,
                        540 * 60)

    def test_is_solution(self):
        chk = {"system": True, "normal_form": True, "sweep": True, "anisotropic": False}
        row = {"cert": "SAT", "satisfies_cnf": True, "check": chk}
        self.assertFalse(m132.is_solution(row))
        row = {"cert": "SAT", "satisfies_cnf": True, "check": dict(chk, anisotropic=True)}
        self.assertTrue(m132.is_solution(row))
        self.assertFalse(m132.is_solution({"cert": "VERIFIED"}))


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
