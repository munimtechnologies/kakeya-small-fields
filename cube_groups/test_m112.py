# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m112.py (job m112, notes/a104.md). Needs m42.py, sat_aniso.py, m100.py to m106.py,
m110.py and m111.py next to it. The case lists, shards and grading are checked on small tables
worked out by hand, and the pi(R) predicate on four instance names read by hand (m102's bit order:
entry (r, c) of a 3 x 3 matrix is bit 3r + c, so entries (2, 0) and (2, 1) are bits 6 and 7)."""
import tempfile
import time
import unittest

import m111
import m112

O = "r3b_t8_B7_o007_c000_"     # 20 characters: the label starts after it


class TestCases(unittest.TestCase):
    def test_shards_partition_399(self):
        names = [f"x{i:03d}" for i in range(m112.TOTAL)]
        lists = {s: m112.shard_list(s, names) for s in m112.SHARDS}
        self.assertEqual(m112.TOTAL, 399)
        self.assertEqual({s: len(v) for s, v in lists.items()}, m112.SIZE)
        self.assertEqual(sorted(x for v in lists.values() for x in v), names)
        self.assertEqual(lists["a"][:2], ["x000", "x012"])

    def test_open_cases(self):
        parts = {"a": {"n": "UNSAT"}, "b": {"n": "UNKNOWN", "sweep": "UNKNOWN"},
                 "c": {"n": "SAT", "sweep": "UNKNOWN"}, "d": {"n": "UNKNOWN", "sweep": "UNSAT"},
                 "e": {"n": "UNKNOWN"}}
        self.assertEqual(m112.open_cases(parts, ["c"]), ["b", "e"])
        self.assertEqual(m112.open_cases(parts, []), ["b", "c", "e"])

    def test_m111_decided(self):
        with tempfile.TemporaryDirectory() as d:
            m111.save(d, "m111b_grade.json", {"decided": ["y", "x"]})
            self.assertIsNone(m112.m111_decided(d))
            m111.save(d, "m111c_grade.json", {"decided": ["w"]})
            self.assertEqual(m112.m111_decided(d), ["w", "x", "y"])

    def test_pres_r_by_name(self):
        # m092 = 64 + 28: bit 6 set, so T(N) moves q_0 out of pi(R) = span(q_0, q_1);
        # 205 = 128 + 64 + 13: bits 6 and 7 set; 12 and 30, 43 are below 64
        cases = m112.d1_cases()
        self.assertEqual(len(cases), 3876)
        for x, want in (("r3b_t8_B7_o010_c003_t2_m092", False),
                        ("r3b_t8_B7_o010_c008_t3_m063_205", False),
                        ("r3b_t8_B7_o007_c000_t2_m012", True),
                        ("r3b_t8_B7_o007_c000_t3_m030_043", True)):
            self.assertEqual(m111.features(*cases[x])["pres_r"], want, x)

    def test_deadline_skips_without_solving(self):
        with tempfile.TemporaryDirectory() as d:
            self.assertIsNone(m112.solve_sweep("not-a-case", 1.0, time.time() - 1, d))


class TestGrade(unittest.TestCase):
    def test_grade_rows(self):
        def row(label, status, wall, **kw):
            r = {"instance": O + label, "tag": f"{O}{label}_sweep", "part": "sweep",
                 "status": status, "wall_seconds": wall, "type": "nil3"}
            r.update(kw)
            return r

        rows = [row("t2_m012", "UNSAT", 500.0), row("t2_m015", "UNKNOWN", 1500.0),
                row("t2_m026", "UNSAT", 300.0), row("t2_m031", "UNSAT", 900.0),
                row("t2_m047", "SAT", 20.0, verified=True, check={"anisotropic": False})]
        mine = [O + s for s in ("t2_m012", "t2_m015", "t2_m026", "t2_m031", "t2_m047", "t2_m059")]
        skipped = [O + "t2_m059_sweep"]
        g, out = m112.grade_rows(rows, skipped, mine)
        self.assertTrue(all(g.values()), g)
        self.assertIn(f"verified_{O}t2_m047_sweep", g)
        self.assertEqual(out["unsat"], [O + "t2_m012", O + "t2_m026", O + "t2_m031"])
        self.assertEqual(out["open"], [O + "t2_m015", O + "t2_m047", O + "t2_m059"])
        self.assertEqual(out["unsat_wall_seconds"], {"min": 300.0, "median": 500.0, "max": 900.0})
        self.assertEqual(out["by_label"]["t2_m012"], {"UNSAT": 1})
        self.assertEqual(out["by_type"], {"nil3": {"UNSAT": 3, "UNKNOWN": 1, "SAT": 1}})
        self.assertEqual(out["full_models"], [])
        # a case neither run nor skipped, an unverified model, and a model anisotropic on all of V
        g, _ = m112.grade_rows(rows, [], mine)
        self.assertFalse(g["all_accounted"])
        bad = rows + [row("t2_m059", "SAT", 30.0, verified=False, check={"anisotropic": True})]
        g, out = m112.grade_rows(bad, [], mine)
        self.assertFalse(g[f"verified_{O}t2_m059_sweep"])
        self.assertEqual(out["full_models"], [O + "t2_m059_sweep"])
        g, _ = m112.grade_rows(rows + [row("t2_m062", "ERROR", 1.0)], skipped, mine)
        self.assertFalse(g["no_error"])


if __name__ == "__main__":
    unittest.main()
