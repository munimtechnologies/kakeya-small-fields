# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m131.py (job m131, cube_groups/m131-predictions.md). Needs m100, m102, m105,
m113 and m130 next to it. Expectations worked out by hand from m130's published grade file:

- the three shards are m130's three pilot cases without a certificate: a = the "n" SAT case
  (o012_c003 t2_m204), b and c = the two UNKNOWN cases (o012_c002 t2_m085, o012_c005 t2_m170);
  all are d = 0 cases (classes with dmeet = 0) and distinct;
- the caps are CaDiCaL 4,800 s and drat-trim 25,000 s at the sweep CNF;
- is_solution accepts only a SAT row whose model passes every m106 check; m130's "n" SAT row
  (anisotropic False) is not a solution.
"""
import unittest

import m130
import m131


class TestM131(unittest.TestCase):
    def test_cases(self):
        self.assertEqual(sorted(m131.CASES), ["a", "b", "c"])
        self.assertEqual(len(set(m131.CASES.values())), 3)
        table = m130.by_name()
        for shard, x in m131.CASES.items():
            self.assertIn(x, table, shard)
            self.assertEqual(table[x][0]["dmeet"], 0)
        self.assertEqual(m131.M130_CERT, {"a": "SAT", "b": "UNKNOWN", "c": "UNKNOWN"})

    def test_caps(self):
        self.assertEqual(m131.MODE, "sweep")
        self.assertEqual(m131.CADICAL_CAP, 4800.0)
        self.assertEqual(m131.DRAT_CAP["sweep"], 25000)

    def test_is_solution(self):
        chk = {"system": True, "normal_form": True, "sweep": True, "anisotropic": False}
        row = {"cert": "SAT", "satisfies_cnf": True, "check": chk}
        self.assertFalse(m131.is_solution(row))
        row = {"cert": "SAT", "satisfies_cnf": True, "check": dict(chk, anisotropic=True)}
        self.assertTrue(m131.is_solution(row))
        self.assertFalse(m131.is_solution({"cert": "VERIFIED"}))
        self.assertFalse(m131.is_solution({"cert": "SAT", "satisfies_cnf": True, "check": {}}))


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
