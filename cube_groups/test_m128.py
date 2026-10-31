# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m128.py's reading and reconciling (no network). Always exits 0: the results are
in the log."""
import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import m128  # noqa: E402


class Read(unittest.TestCase):
    def test_rows_dict_of_lists(self):
        g = {"rows": {"a": ["VERIFIED", "sweep", 4], "b": ["SKIPPED", "sweep"]}}
        self.assertEqual(m128.statuses(g), {"a": "VERIFIED", "b": "SKIPPED"})

    def test_rows_list_of_dicts(self):
        g = {"rows": [{"instance": "a", "cert": "VERIFIED"}, {"instance": "b"}]}
        self.assertEqual(m128.statuses(g), {"a": "VERIFIED"})

    def test_other_shapes(self):
        self.assertEqual(m128.statuses({"rows": 3}), {})
        self.assertEqual(m128.statuses([]), {})
        self.assertEqual(m128.statuses({"rows": {"a": [1, 2]}}), {})


class Reconcile(unittest.TestCase):
    def test_counts(self):
        d1 = {"a", "b", "c", "d"}
        files = {"f1": {"a": "VERIFIED", "b": "SKIPPED", "z": "VERIFIED"},
                 "f2": {"b": "VERIFIED", "c": "UNKNOWN"},
                 "f3": {"a": "VERIFIED", "d": "SAT"}}
        r = m128.reconcile(d1, files)
        self.assertEqual(r["verified"], ["a", "b"])
        self.assertEqual(r["missing"], ["c", "d"])
        self.assertEqual(r["bad"], ["d"])
        self.assertEqual(r["first_verified_by_file"], {"f1": 1, "f2": 1})
        self.assertNotIn("z", r["seen"])

    def test_local_name(self):
        self.assertEqual(m128.local_name("cube_groups/results/m127a/m127a_grade.json"),
                         "m127a__m127a_grade.json")

    def test_m127_paths(self):
        self.assertEqual(len(m128.M127), 8)
        self.assertTrue(all(p.startswith(m128.RESULTS) for p in m128.M127))


if __name__ == "__main__":
    result = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {result.testsRun} failures {len(result.failures)} "
          f"errors {len(result.errors)}", flush=True)
    sys.exit(0)
