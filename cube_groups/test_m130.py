# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m130.py (job m130, cube_groups/m130-predictions.md). Needs m100, m102, m105 and
m113 next to it. Expectations worked out by hand:

- pilot_names takes indices floor(k * len / 6): for 1,500 names, 0, 250, 500, 750, 1000, 1250;
  for 7 names 0, 1, 2, 3, 4, 5; for 6 or fewer names, all of them, sorted.
- The d = 0 classes exist and all have dmeet = 0; their names are distinct; none is a d = 1 class
  (the d = 1 classes are those of m113.d1_cases()'s specs).
- The caps are m110's "n" pass (600 s CaDiCaL) with m113's "n" drat-trim limit (1,200 s).
"""
import unittest

import m113
import m130


class TestM130(unittest.TestCase):
    def test_pilot_names(self):
        names = [f"u{k:04d}" for k in range(1500)]
        self.assertEqual(m130.pilot_names(names),
                         ["u0000", "u0250", "u0500", "u0750", "u1000", "u1250"])
        self.assertEqual(m130.pilot_names([f"u{k}" for k in range(7)]),
                         ["u0", "u1", "u2", "u3", "u4", "u5"])
        self.assertEqual(m130.pilot_names(["b", "a"]), ["a", "b"])
        shuffled = list(reversed(names))
        self.assertEqual(m130.pilot_names(shuffled), m130.pilot_names(names))

    def test_caps(self):
        self.assertEqual(m130.CADICAL_CAP, 600.0)
        self.assertEqual(m130.DRAT_CAP["n"], 1200)
        self.assertEqual(m130.MODE, "n")
        self.assertEqual(m130.EXPECT_D0, 1500)

    def test_d0_specs(self):
        specs = m130.d0_specs()
        self.assertGreater(len(specs), 0)
        self.assertTrue(all(s["dmeet"] == 0 for s in specs))
        names = [s["name"] for s in specs]
        self.assertEqual(len(set(names)), len(names))
        d1_classes = {s["name"] for s, _ in m113.d1_cases().values()}
        self.assertFalse(set(names) & d1_classes)


if __name__ == "__main__":
    # always exit 0: the results are in the log, and a failing test must not stop the job
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
