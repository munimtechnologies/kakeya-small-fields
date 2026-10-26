# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m113.py (job m113, cube_groups/m113-predictions.md). Needs m42.py, sat_aniso.py,
m100.py to m108.py, m110.py and m111.py next to it. The mode rule, shards and grading are checked
on small tables worked out by hand; the certified "n" CNF against the one m106 (and so m110) solved,
clause for clause; the counts against m110's grade files when they are present (job setup fetches
them), as read by hand from those files on 2026-10-26: 3,062 cases UNSAT at "n", 13 at the sweep."""
import os
import time
import unittest

import m100
import m102
import m106
import m113

O = "r3b_t8_B7_o007_c000_"     # 20 characters: the label starts after it


class TestStatic(unittest.TestCase):
    def test_mode_and_decided(self):
        parts = {"a": {"n": "UNSAT"}, "b": {"n": "SAT", "sweep": "UNSAT"},
                 "c": {"n": "UNKNOWN", "sweep": "UNKNOWN"}, "d": {"n": "SAT", "sweep": "UNKNOWN"},
                 "e": {"n": "UNKNOWN"}, "f": {"n": "UNKNOWN", "sweep": "UNSAT"}}
        self.assertEqual(m113.mode_of(parts["a"]), "n")
        self.assertEqual(m113.mode_of(parts["b"]), "sweep")
        self.assertIsNone(m113.mode_of(parts["e"]))
        self.assertEqual(m113.decided(parts), [("a", "n"), ("b", "sweep"), ("f", "sweep")])

    def test_shards_partition_3075(self):
        items = [(f"x{i:04d}", "n") for i in range(m113.TOTAL)]
        lists = {s: m113.shard_list(s, items) for s in m113.SHARDS}
        self.assertEqual(sum(m113.BY_MODE.values()), m113.TOTAL)
        self.assertEqual({s: len(v) for s, v in lists.items()}, m113.SIZE)
        self.assertEqual(sorted(x for v in lists.values() for x in v), items)
        self.assertEqual(lists["a"][:2], [("x0000", "n"), ("x0006", "n")])

    def test_grade_rows(self):
        def row(label, mode, cert, cad, drat, clauses, **kw):
            r = {"instance": O + label, "name": O[:19], "kind": label[:2], "mode": mode,
                 "cert": cert, "cadical": {"seconds": cad}, "proof_bytes": 1000, "clauses": clauses,
                 "inv": 2, "type": "irr"}
            if drat is not None:
                r["drat"] = {"seconds": drat, "verified": cert == "VERIFIED"}
            r.update(kw)
            return r

        rows = [row("t2_m012", "n", "VERIFIED", 8.0, 12.0, 546000),
                row("t2_m015", "n", "VERIFIED", 10.0, 20.0, 546000),
                row("t2_m026", "n", "VERIFIED", 6.0, 9.0, 546000),
                row("t3_m001_016", "sweep", "VERIFIED", 70.0, 90.0, 907000),
                {"instance": O + "t2_m031", "name": O[:19], "mode": "n", "cert": "SKIPPED"}]
        mine = [[O + "t2_m012", "n"], [O + "t2_m015", "n"], [O + "t2_m026", "n"],
                [O + "t2_m031", "n"], [O + "t3_m001_016", "sweep"]]
        g, out = m113.grade_rows(rows, mine)
        self.assertTrue(all(g.values()), g)
        self.assertEqual(out["verified"], 4)
        self.assertEqual(out["skipped"], [O + "t2_m031"])
        self.assertEqual(out["not_verified"], [])
        self.assertEqual(out["cadical"]["n"], {"n": 3, "mean": 8.0, "median": 8.0, "max": 10.0})
        self.assertEqual(out["drat"]["sweep"], {"n": 1, "mean": 90.0, "median": 90.0, "max": 90.0})
        self.assertEqual(out["by_mode"], {"n": {"VERIFIED": 3, "SKIPPED": 1},
                                          "sweep": {"VERIFIED": 1}})
        # a failed check, a SAT answer, a clause count off within one class and kind, a lost case
        bad = rows[:3] + [row("t3_m001_016", "sweep", "NOT_VERIFIED", 70.0, 90.0, 907000),
                          row("t2_m031", "n", "SAT", 3.0, None, 546001)]
        g, out = m113.grade_rows(bad, mine)
        self.assertFalse(g["all_verified"] or g["no_sat"] or g["clauses_uniform"])
        self.assertTrue(g["all_accounted"])
        self.assertEqual(out["not_verified"], [[O + "t2_m031", "SAT"],
                                               [O + "t3_m001_016", "NOT_VERIFIED"]])
        g, _ = m113.grade_rows(rows[:4], mine)
        self.assertFalse(g["all_accounted"])


class TestCases(unittest.TestCase):
    def test_control_case(self):
        spec, case = m113.d1_cases()[m113.CONTROL]
        self.assertEqual(len(m113.d1_cases()), 3876)
        self.assertEqual(spec["dmeet"], 1)
        self.assertEqual(case["kind"], "t2")

    def test_deadline_skips_without_building(self):
        row = m113.certify_item("no-tools", m113.CONTROL, "n", time.time() - 1)
        self.assertEqual(row["cert"], "SKIPPED")
        self.assertEqual(row["mode"], "n")

    def test_n_cnf_is_what_m110_solved(self):
        # m106.child (which m110's "n" part runs): m102's relax CNF plus sigma != 0 on N
        spec, case = m113.d1_cases()[m113.CONTROL]
        ref, names, _ = m102.build(spec, case, "relax")
        m106.add_aniso_masks(ref, names, m102.T, m106.n_masks())
        got, _ = m113.m108.build_cert(spec, case, "n")
        self.assertEqual((m100.clause_hash(got), len(got.clauses), got.nv),
                         (m100.clause_hash(ref), len(ref.clauses), ref.nv))

    @unittest.skipUnless(all(os.path.exists(f"m110{s}_grade.json") for s in m113.M110_DONE),
                         "m110 grade files not fetched")
    def test_counts_from_m110(self):
        items = m113.decided(m113.m111.m110_parts(m113.M110_DONE))
        modes = [m for _, m in items]
        self.assertEqual(len(items), m113.TOTAL)
        self.assertEqual(modes.count("n"), m113.BY_MODE["n"])
        self.assertEqual(modes.count("sweep"), m113.BY_MODE["sweep"])
        self.assertTrue(all(x in m113.d1_cases() for x, _ in items))


if __name__ == "__main__":
    unittest.main()
