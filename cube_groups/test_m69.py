# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m69.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69


def fake_reps(group):
    """m66-shaped reps for the group's classes, ranks following each class's GATE counts (rank 0
    first, as m66's order does not matter to the plan)."""
    reps = {}
    for name in m69.TAILS[group]:
        by = m69.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    return reps


class TestM69(unittest.TestCase):
    def test_installed(self):
        m69.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertIsNot(m69._base_build_plain, m69.build_plain69)

    def test_lists(self):
        cl = m66.classes()
        for g in "ab":
            for name in m69.TAILS[g]:
                self.assertIn(name, cl)
                self.assertIn(name, m69.SWEEP)
                self.assertEqual(sum(m69.GATE[name]["by_rank"].values()),
                                 m69.GATE[name]["orbits"])
                self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], m69.GATE[name]["d"])
        self.assertTrue(all(m69.drop_rank0(n) for n in m69.TAILS["a"]))
        self.assertEqual(m69.A561["name"], "r3s_t7_B5_o020_c000_a561")

    def test_mask_round_trip(self):
        name = m69.TAILS["b"][0]
        mp = m66.Maps(m69.r_of(name))
        for idx in (1, 9, 511, 4096, 70000, (1 << 18) - 1):
            cols = mp.cols(idx)
            a1 = m69.mask_of(cols)
            self.assertEqual(m66.cols_of_mask(a1), cols)
            self.assertEqual(tuple(m.column(a1, c) for c in range(7)), cols)
            self.assertEqual(m69.rank_on(a1, m69.X1), mp.rank_x1(idx))
            self.assertEqual(m69.rank_on(a1, m69.X1), m.rank_on_x1(a1))

    def test_admissible(self):
        for name in m69.TAILS["b"]:
            au, rb, d = m66.classes()[name], m69.r_of(name), m69.GATE[name]["d"]
            self.assertFalse(m69.admissible_b6(0, au, rb, d))
            self.assertFalse(m69.admissible_b6(au, au, rb, d))
        name = m69.TAILS["a"][0]
        self.assertTrue(m69.admissible_b6(0, m66.classes()[name], m69.r_of(name), 0))
        sp = m69.A561
        self.assertTrue(m69.admissible_b5(sp["a1"], sp["au"], tuple(sp["x1"]), tuple(sp["r"])))
        self.assertEqual(m69.rank_on(sp["a1"], tuple(sp["x1"])), 1)

    def test_plan(self):
        for g in "ab":
            reps = fake_reps(g)
            p = m69.plan(g, reps)
            named = [e for e in p if e[4]]
            tail = [e[0] for e in p if not e[4]]
            self.assertEqual(len(named), 2 * len(m69.NAMED[g]))
            self.assertTrue(all(e[4] for e in p[:len(named)]))
            self.assertEqual(len(tail), sum(m69.planned(n) for n in m69.TAILS[g]))
            self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))
            self.assertEqual(tail[0]["parent"], m69.TAILS[g][0])
            self.assertEqual(tail[0]["rank_x1"], 2)
            for name in m69.TAILS[g]:
                mine = [s for s in tail if s["parent"] == name]
                ranks = [s["rank_x1"] for s in mine]
                self.assertEqual(ranks, sorted(ranks, reverse=True))
                if m69.drop_rank0(name):
                    self.assertTrue(all(r > 0 for r in ranks))
                else:
                    self.assertEqual(ranks.count(0), m69.GATE[name]["by_rank"]["0"])
                    self.assertTrue(all(s["name"].startswith("r3l_") for s in mine
                                        if s["rank_x1"] == 0))
            if g == "a":
                self.assertEqual([e[1] for e in named], ["cadical", "xor"])
                self.assertFalse(any(s.get("lemma93") for s in tail))

    def test_units(self):
        name = m69.TAILS["b"][1]
        rep = {"index": 0, "a1": 0, "rank_x1": 0, "size": 1}
        sp = m69.split_spec(name, 0, rep, True)
        self.assertEqual(m69.lemma93_units(sp), 21)
        self.assertEqual(m69.x1_cols(sp), [3, 2, 1])
        _, _, h, u = m.build(sp, "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49 + 21))
        ok, _ = m69.probe93(sp)
        self.assertTrue(all(ok.values()))
        plain = m69.split_spec(name, 0, dict(rep, rank_x1=1))
        _, _, h, u = m.build(plain, "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49))
        _, _, h, u = m.build(dict(m69.A561), "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B5"], 49))

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
                out = m69.grade(g, d)
                self.assertEqual(out["b6_closed"], list(m69.TAILS[g]))
                self.assertFalse(out["any_sat_7"])
                self.assertEqual(out["named_unsat"], len(m69.NAMED[g]))
                for c in out["classes"].values():
                    self.assertEqual(c["open"], [])
                    self.assertEqual(c["median_unsat_wall"], 1.0)
                if g == "a":
                    self.assertTrue(out["o020"]["empty"])
                    self.assertEqual(out["b5_closed"], [m69.O20])
                self.assertIn("SUMMARY grade", m69.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m69.grade(g, d)
                last = m69.TAILS[g][-1]
                self.assertFalse(out["classes"][last]["empty"])
                self.assertEqual(out["classes"][last]["skipped"], 1)
                self.assertNotIn(last, out["b6_closed"])


if __name__ == "__main__":
    unittest.main()
