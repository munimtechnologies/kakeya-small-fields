# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m89.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m89


def fake_reps(group):
    """m66-shaped reps of the group's classes: roots of rank 2 except at the re-runs, which carry
    the recorded index, map, rank and size."""
    reps = {}
    for name in {row[0] for row in m89.named_rows(group)}:
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m89.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in m89.named_rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestM89(unittest.TestCase):
    def test_installed(self):
        m89.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertEqual(m69.TAILS, {"a": (), "b": ()})
        self.assertIs(m69.plan, m89.plan)
        self.assertEqual(m69.REPS_FILE, "m89_reps.json")

    def test_lists(self):
        cl = m66.classes()
        self.assertTrue(m89.lists_ok())
        self.assertEqual(len(m89.CLOSED_SPLIT), 41)
        self.assertEqual(len(set(m89.CLOSED_SPLIT)), 41)
        self.assertTrue(set(m89.CLOSED_SPLIT) <= set(cl))
        self.assertFalse(set(m89.CLOSED_SPLIT) & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        for name in m89.NAMED_CLASSES:
            gate = m89.NAMED_GATE[name]
            self.assertIn(name, cl)
            self.assertNotIn(name, m58.CLOSED_KNOWN)
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
            self.assertEqual(m66.HAND_ADM[gate["d"]], gate["valid"])

    def test_named(self):
        rows = m89.OPEN_PREV["a"] + m89.OPEN_PREV["b"]
        self.assertEqual(len(rows), 49)
        self.assertEqual(len({(r[0], r[1]) for r in rows}), 49)
        for name, (total, unsat) in m89.BEFORE.items():
            self.assertEqual(sum(r[0] == name for r in rows), total - unsat)
        for g in ("a", "b"):
            gr = m89.named_rows(g)
            self.assertEqual(len(gr), m89.NAMED_COUNT[g])
            for rk, c in m89.NAMED_RANKS[g].items():
                self.assertEqual(sum(r[2] == rk for r in gr), c)
            for name, c in m89.NAMED_PER_CLASS[g].items():
                self.assertEqual(sum(r[0] == name for r in gr), c)
                ks = [r[1] for r in gr if r[0] == name]
                self.assertEqual(ks, sorted(ks))
        maps = {}
        for name, k, rk, index, size, a1 in rows:
            au, rb = m66.classes()[name], m69.r_of(name)
            if name not in maps:
                maps[name] = m66.Maps(rb)
            mp = maps[name]
            self.assertIn(rk, (0, 1, 2))
            self.assertEqual(m69.rank_on(a1, m69.X1), rk)
            self.assertTrue(m69.admissible_b6(a1, au, rb, m89.NAMED_GATE[name]["d"]))
            self.assertEqual(mp.index(m66.cols_of_mask(a1)), index)
            self.assertEqual(mp.rank_x1(index), rk)
            self.assertLess(k, m89.NAMED_GATE[name]["orbits"])
        for g in ("a", "b"):
            specs = m89.named_specs(g, fake_reps(g))
            self.assertEqual([sp["name"] for sp in specs],
                             [m89.named_name(r[0], r[1], r[2]) for r in m89.named_rows(g)])
            self.assertTrue(all(bool(sp.get("lemma93")) == (sp["rank_x1"] == 0) for sp in specs))
            self.assertTrue(all(sp["name"].startswith("r3l_") == (sp["rank_x1"] == 0)
                                for sp in specs))

    def test_plan(self):
        for g in ("a", "b"):
            p = m69.plan(g, fake_reps(g))
            self.assertEqual(len(p), 2 * m89.NAMED_COUNT[g])
            self.assertTrue(all(e[4] for e in p))
            self.assertEqual([e[1] for e in p[:2]], ["cadical", "xor"])
            self.assertEqual([e[3] for e in p[:2]], [None, "open"])
            self.assertTrue(all(e[2] == m69.NAMED_CAP for e in p))

    def test_units(self):
        for g in ("a", "b"):
            specs = m89.named_specs(g, fake_reps(g))
            sp = next(s for s in specs if s.get("lemma93"))
            self.assertEqual(m69.lemma93_units(sp), 21)
            _, _, h, u = m.build(dict(sp), "cadical")
            self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49 + 21))
            ok, _ = m69.probe93(sp)
            self.assertTrue(all(ok.values()))
            for s in specs:
                if not s.get("lemma93"):
                    _, _, h, u = m.build(dict(s), "cadical")
                    self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49))
        self.assertEqual(sum(1 for s in m89.named_specs("a", fake_reps("a"))
                             if not s.get("lemma93")), 1)
        self.assertEqual(sum(1 for s in m89.named_specs("b", fake_reps("b"))
                             if not s.get("lemma93")), 0)

    def write_run(self, d, group, reps):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        for spec, arm, _, _, _ in m69.plan(group, reps):
            if arm == "cadical":
                with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                    json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 300.0}, f)

    def test_grade(self):
        for g in ("a", "b"):
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m89.grade(g, d)
                self.assertEqual(out["classes"], {})
                self.assertEqual(out["b6_closed"], [])
                self.assertFalse(out["any_sat_7"])
                self.assertNotIn("o020", out)
                self.assertNotIn("b5_closed", out)
                self.assertEqual(out["named_unsat"], m89.NAMED_COUNT[g])
                self.assertEqual(out["named_open"], [])
                self.assertEqual(out["named_max_unsat_wall"], 1.0)
                self.assertEqual(out["named_unsat_by_arm"],
                                 {"cadical": m89.NAMED_COUNT[g], "xor": 0})
                self.assertEqual({n: c["unsat_here"] for n, c in out["named_classes"].items()},
                                 m89.NAMED_PER_CLASS[g])
                self.assertTrue(all(c["open"] == [] for c in out["named_classes"].values()))
                self.assertIn("SUMMARY grade", m89.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                first = m89.named_specs(g, reps)[0]
                self.write_run(d, g, reps)
                os.remove(os.path.join(d, m.tag_of(first, "cadical") + ".json"))
                out = m89.grade(g, d)
                c = out["named_classes"][first["parent"]]
                self.assertEqual(c["unsat_here"], m89.NAMED_PER_CLASS[g][first["parent"]] - 1)
                self.assertEqual(c["open"], [first["name"]])
                self.assertEqual(out["named_open"], [first["name"]])
                self.assertIn("SUMMARY grade", m89.summary_line(out))


if __name__ == "__main__":
    unittest.main()
