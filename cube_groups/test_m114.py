# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m114.py (job m114, notes/a105.md). Needs m42.py, sat_aniso.py, m100.py to m106.py,
m110.py, m111.py and m112.py next to it, and the fetched grade files m110i_grade.json and
m112{a..h}_grade.json for the last test. The case lists and shards are checked on small tables
worked out by hand; the counts 54 and 26 and the names below were read by hand off the published
grade files (m110i "open"; m112a-h "skipped")."""
import os
import tempfile
import time
import unittest

import m111
import m112
import m114

P = "r3b_t8_B7_"


def fake(d, opened, cases, skipped, unsat):
    """m110i and m112a-h grade files in d: m112a carries the given lists, b-h are empty."""
    m111.save(d, "m110i_grade.json", {"open": opened, "cases": cases})
    for s in m114.M112_RUN:
        m111.save(d, f"m112{s}_grade.json",
                  {"skipped": skipped if s == "a" else [], "unsat": unsat if s == "a" else []})


class TestCases(unittest.TestCase):
    def test_shards_partition_80(self):
        names = [f"x{i:02d}" for i in range(m114.TOTAL)]
        lists = {s: m114.shard_list(s, names) for s in m114.SHARDS}
        self.assertEqual(m114.TOTAL, 80)
        self.assertEqual({s: len(v) for s, v in lists.items()}, m114.SIZE)
        self.assertEqual(sorted(x for v in lists.values() for x in v), names)
        self.assertEqual(lists["a"][:3], ["x00", "x06", "x12"])
        self.assertEqual(lists["f"][-1], "x77")

    def test_sources_and_split(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m114.sources(d))
            fake(d, ["c", "b"], {"b": {"n": "UNKNOWN", "sweep": "UNKNOWN"}, "c": {"n": "SAT"},
                                 "z": {"n": "UNSAT"}, "y": {"n": "UNKNOWN", "sweep": "UNSAT"}},
                 ["e_sweep", "d_sweep"], ["w"])
            src = m114.sources(d)
            self.assertEqual(m114.split(*src), (["b", "c"], ["d", "e"]))
            self.assertEqual(m114.unsat_before(*src), {"z", "y", "w"})

    def test_sources_missing_m112(self):
        with tempfile.TemporaryDirectory() as d:
            fake(d, [], {}, [], [])
            os.remove(os.path.join(d, "m112h_grade.json"))
            self.assertIsNone(m114.sources(d))

    def test_deadline_skips_without_solving(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m112.solve_sweep("not-a-case", 1.0, time.time() - 1, d))


class TestPublished(unittest.TestCase):
    def test_published_lists(self):
        src = m114.sources(".")
        self.assertIsNotNone(src, "grade files not fetched")
        opened, skipped = m114.split(*src)
        self.assertEqual((len(opened), len(skipped)), (54, 26))
        for x in ("o007_c000_t2_m038", "o009_c009_t2_m012", "o010_c008_t3_m011_017"):
            self.assertIn(P + x, opened)
        for x in ("o010_c005_t2_m031", "o010_c008_t3_m063_205", "o010_c008_t2_m026"):
            self.assertIn(P + x, skipped)
        # the ten UNKNOWN at 1,500 s are not taken again
        for x in ("o007_c004_t2_m011", "o009_c001_t2_m026", "o008_c001_t3_m011_017"):
            self.assertNotIn(P + x, opened + skipped)
        self.assertFalse(set(opened + skipped) & m114.unsat_before(*src))
        cases = m112.d1_cases()
        self.assertTrue(all(x in cases for x in opened + skipped))


if __name__ == "__main__":
    unittest.main()
