# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m70.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m70


def fake_reps(group):
    """m66-shaped reps for the group's classes, ranks following each class's GATE counts."""
    reps = {}
    for name in m70.TAILS[group]:
        by = m70.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return reps


class TestM70(unittest.TestCase):
    def test_installed(self):
        m70.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertIs(m69.NAMED, m70.NAMED)
        self.assertIs(m69.TAILS, m70.TAILS)
        self.assertIs(m69.GATE, m70.GATE)
        self.assertIs(m69.SWEEP, m70.SWEEP)
        self.assertEqual(m69.REPS_FILE, "m70_reps.json")

    def test_lists(self):
        cl = m66.classes()
        names = set(m70.TAILS["a"]) | set(m70.TAILS["b"])
        self.assertEqual(names, set(m70.GATE))
        self.assertEqual(names, set(m70.SWEEP))
        self.assertFalse(names & set(m70.CLOSED_M69A))
        self.assertFalse(names & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        for name in names:
            self.assertIn(name, cl)
            self.assertEqual(sum(m70.GATE[name]["by_rank"].values()), m70.GATE[name]["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], m70.GATE[name]["d"])
            self.assertEqual(m66.HAND_ORDER[name], m70.GATE[name]["order"])
        self.assertEqual([n for n in names if m69.drop_rank0(n)], ["r3b_t7_B6_o011_c002"])

    def test_named(self):
        named = m70.NAMED["a"]
        self.assertEqual(len(named), 27)
        self.assertEqual(m70.NAMED["b"], ())
        self.assertEqual(len({sp["name"] for sp in named}), 27)
        x1, rb = m70.O002_X1, m70.O002_R
        self.assertEqual(m.kernel(m70.O002_AU, 7), x1)
        self.assertEqual(m.column_space(m70.O002_AU, 7), rb)
        for sp in named:
            self.assertEqual((sp["pair"], sp["cls"], sp["p"]), (2, 1, 5))
            self.assertEqual(tuple(sp["x1"]), x1)
            self.assertEqual(tuple(sp["r"]), rb)
            self.assertTrue(m69.admissible_b5(sp["a1"], m70.O002_AU, x1, rb))
            self.assertEqual(m69.rank_on(sp["a1"], x1), sp["rank_x1"])
            self.assertEqual(bool(sp.get("lemma93")), sp["rank_x1"] == 0)
        self.assertEqual(sum(sp["rank_x1"] == 0 for sp in named), 17)
        self.assertTrue(m69.distinct_with_au([sp["a1"] for sp in named], m70.O002_AU))

    def test_plan(self):
        for g in "ab":
            reps = fake_reps(g)
            p = m69.plan(g, reps)
            named = [e for e in p if e[4]]
            tail = [e[0] for e in p if not e[4]]
            self.assertEqual(len(named), 2 * len(m70.NAMED[g]))
            self.assertTrue(all(e[4] for e in p[:len(named)]))
            self.assertEqual(len(tail), sum(m69.planned(n) for n in m70.TAILS[g]))
            self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))
            self.assertEqual(tail[0]["parent"], m70.TAILS[g][0])
            self.assertEqual(tail[0]["rank_x1"], 2)
            if g == "a":
                self.assertEqual([e[1] for e in named[:2]], ["cadical", "xor"])
                self.assertEqual(named[1][3], "open")
                self.assertEqual(len(tail), 924 + 674 + 674)
            else:
                self.assertEqual(len(tail), 747 + 3 * 847)

    def test_units(self):
        named = m70.NAMED["a"]
        sp = next(s for s in named if s.get("lemma93"))
        self.assertEqual(m69.lemma93_units(sp), 42)
        _, _, h, u = m.build(dict(sp), "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B5"], 49 + 42))
        ok, _ = m70.probe93(sp, "B5")
        self.assertTrue(all(ok.values()))
        plain = next(s for s in named if not s.get("lemma93"))
        _, _, h, u = m.build(dict(plain), "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B5"], 49))
        rep = {"index": 0, "a1": 0, "rank_x1": 0, "size": 1}
        b6 = m69.split_spec(m70.TAILS["b"][1], 0, rep, True)
        ok, _ = m70.probe93(b6, "B6")
        self.assertTrue(all(ok.values()))

    def write_run(self, d, g, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = [e for e in m69.plan(g, reps) if e[1] == "cadical"]
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        for g in "ab":
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m70.grade(g, d)
                self.assertEqual(out["b6_closed"], list(m70.TAILS[g]))
                self.assertFalse(out["any_sat_7"])
                self.assertNotIn("o020", out)
                self.assertEqual(out["named_unsat"], len(m70.NAMED[g]))
                if g == "a":
                    self.assertTrue(out["o002"]["empty"])
                    self.assertEqual(out["b5_closed"], [m70.O002])
                    self.assertEqual(out["named_open"], [])
                    self.assertEqual(out["named_max_unsat_wall"], 1.0)
                else:
                    self.assertNotIn("o002", out)
                self.assertIn("SUMMARY grade", m70.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m70.grade(g, d)
                last = m70.TAILS[g][-1]
                self.assertFalse(out["classes"][last]["empty"])
                self.assertEqual(out["classes"][last]["skipped"], 1)
        with tempfile.TemporaryDirectory() as d:
            reps = fake_reps("a")
            self.write_run(d, "a", reps)
            os.remove(os.path.join(d, m.tag_of(m70.NAMED["a"][0], "cadical") + ".json"))
            out = m70.grade("a", d)
            self.assertFalse(out["o002"]["empty"])
            self.assertEqual(out["o002"]["unsat"], 1907)
            self.assertEqual(out["named_open"], [m70.NAMED["a"][0]["name"]])


if __name__ == "__main__":
    unittest.main()
