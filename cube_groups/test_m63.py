# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m63.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m55
import m57 as m
import m60
import m62
import m63


def rep_of(row):
    name, k, idx, rk, a1 = row
    return {"a1": a1, "rank_x1": rk, "index": idx, "size": 1}


class TestM63(unittest.TestCase):
    def test_installed(self):
        m63.install()
        self.assertIs(m.build_plain, m63.build_plain93)
        self.assertIs(m60.REOPEN, m62.REOPEN)

    def test_entries(self):
        for g in "ab":
            rows = m63.entries(g)
            self.assertTrue(rows)
            self.assertTrue(all(rk == 0 for _, _, _, rk, _ in rows))
            self.assertEqual(len(rows), sum(1 for r in m62.REOPEN[g] if r[3] == 0))
            for name, k, idx, rk, a1 in rows:
                self.assertEqual(m60.rank_on(a1, m55.CLASSES[name][1]), 0)

    def test_x1_cols(self):
        self.assertEqual(m63.x1_cols({"x1": list(m55.ALPHA)}), [3, 2, 1])
        self.assertEqual(m63.x1_cols({"x1": list(m55.BETA)}), [6, 2, 1])

    def test_spec93(self):
        row = m62.REOPEN["a"][0]
        sp = m63.spec93(row[0], row[1], rep_of(row))
        self.assertTrue(sp["name"].startswith("r3l_t7_B5_"))
        self.assertTrue(sp["lemma93"])
        self.assertEqual(sp["d"] - sp["p"], 4)

    def test_units_added(self):
        row = m63.entries("b")[0]
        base = m60.split_spec(row[0], row[1], rep_of(row))
        sp = m63.spec93(row[0], row[1], rep_of(row))
        c0, _, h0, u0 = m.build(base, "cadical")
        c1, names, h1, u1 = m.build(sp, "cadical")
        extra = c1.clauses[len(c0.clauses):]
        self.assertEqual(c1.clauses[:len(c0.clauses)], c0.clauses)
        self.assertEqual(len(extra), m63.lemma93_units(sp))
        self.assertEqual(u1 - u0, len(extra))
        self.assertEqual(h1, h0)
        want = {names[0][i][r][c] for i in (2, 3) for r in range(7) for c in m63.x1_cols(sp)}
        self.assertEqual({-cl[0] for cl in extra}, want)
        self.assertTrue(m.units_consistent(c1))

    def test_no_flag_no_change(self):
        row = m63.entries("a")[0]
        base = m60.split_spec(row[0], row[1], rep_of(row))
        c0, _, _, u0 = m.build(base, "cadical")
        self.assertEqual(u0, 49)

    def fake_reps(self, group):
        reps = {}
        for name, k, idx, rk, a1 in m63.entries(group):
            reps.setdefault(name, [None] * 600)[k] = {"a1": a1, "rank_x1": rk, "index": idx,
                                                     "size": 1}
        return reps

    def test_plan_and_grade(self):
        for g in "ab":
            reps = self.fake_reps(g)
            p = m63.plan(g, reps)
            self.assertEqual(len(p), 2 * len(m63.entries(g)))
            self.assertEqual([e[1] for e in p[:2]], ["cadical", "xor"])
            with tempfile.TemporaryDirectory() as d:
                with open(os.path.join(d, "check.json"), "w") as f:
                    json.dump({"graded": {"x": True}}, f)
                with open(os.path.join(d, m62.REPS_FILE), "w") as f:
                    json.dump(reps, f)
                for spec, arm, _, _ in p:
                    if arm == "cadical":
                        with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                            json.dump({"status": "UNSAT", "wall_seconds": 1.0}, f)
                out = m63.grade(g, d)
                self.assertEqual(len(out["unsat"]), len(m63.entries(g)))
                self.assertEqual(out["open"], [])
                self.assertFalse(out["any_sat_7"])


if __name__ == "__main__":
    unittest.main()
