# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m87.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m87


def fake_reps(group):
    """m66-shaped reps: the tails' ranks follow their GATE counts; the named classes have roots of
    rank 2 except at the re-runs, which carry the recorded index, map, rank and size."""
    reps = {}
    for name in m87.TAILS[group]:
        by = m87.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    for name in m87.NAMED_CLASSES[group]:
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m87.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in m87.named_rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestM87(unittest.TestCase):
    def test_installed(self):
        m87.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertIs(m69.TAILS, m87.TAILS)
        self.assertIs(m69.GATE, m87.GATE)
        self.assertIs(m69.SWEEP, m87.SWEEP)
        self.assertIs(m69.plan, m87.plan)
        self.assertEqual(m69.REPS_FILE, "m87_reps.json")

    def test_lists(self):
        cl = m66.classes()
        tails = set(m87.TAILS["a"]) | set(m87.TAILS["b"])
        self.assertEqual(len(tails), 4)
        self.assertFalse(set(m87.TAILS["a"]) & set(m87.TAILS["b"]))
        self.assertEqual(tails, set(m87.GATE))
        self.assertEqual(tails, set(m87.SWEEP))
        self.assertEqual(len(set(m87.CLOSED_SPLIT)), 39)
        self.assertEqual(len(m87.CLOSED_SPLIT), 39)
        self.assertFalse(set(m87.CLOSED_SPLIT) & set(m87.SPLIT_ELSEWHERE))
        self.assertFalse(tails & (set(m87.CLOSED_SPLIT) | set(m87.SPLIT_ELSEWHERE)))
        named = set(m87.NAMED_CLASSES["a"]) | set(m87.NAMED_CLASSES["b"])
        self.assertFalse(set(m87.NAMED_CLASSES["a"]) & set(m87.NAMED_CLASSES["b"]))
        self.assertEqual(named, set(m87.NAMED_GATE))
        self.assertEqual(named, set(m87.BEFORE))
        both = tails | named
        self.assertFalse(both & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        self.assertFalse(named & set(m87.CLOSED_SPLIT))
        self.assertTrue(set(m87.CLOSED_SPLIT) | set(m87.SPLIT_ELSEWHERE) <= set(cl))
        for name in both:
            self.assertIn(name, cl)
            gate = m87.GATE.get(name) or m87.NAMED_GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
            self.assertEqual(m66.HAND_ADM[gate["d"]], gate["valid"])
        self.assertFalse(any(m69.drop_rank0(n) for n in tails))

    def test_named(self):
        rows = m87.OPEN_PREV
        self.assertEqual(len(rows), 45)
        self.assertEqual(len({(r[0], r[1]) for r in rows}), 45)
        for name, (total, unsat) in m87.BEFORE.items():
            self.assertEqual(sum(r[0] == name for r in rows), total - unsat)
        for g in ("a", "b"):
            self.assertEqual(len(m87.named_rows(g)), m87.NAMED_COUNT[g])
            self.assertEqual(sum(m87.NAMED_RANKS[g].values()), m87.NAMED_COUNT[g])
            for rk, c in m87.NAMED_RANKS[g].items():
                self.assertEqual(sum(r[2] == rk for r in m87.named_rows(g)), c)
        maps = {}
        for name, k, rk, index, size, a1 in rows:
            au, rb = m66.classes()[name], m69.r_of(name)
            if name not in maps:
                maps[name] = m66.Maps(rb)
            mp = maps[name]
            self.assertIn(rk, (0, 1, 2))
            self.assertEqual(m69.rank_on(a1, m69.X1), rk)
            self.assertTrue(m69.admissible_b6(a1, au, rb, m87.NAMED_GATE[name]["d"]))
            self.assertEqual(mp.index(m66.cols_of_mask(a1)), index)
            self.assertEqual(mp.rank_x1(index), rk)
            self.assertLess(k, m87.NAMED_GATE[name]["orbits"])
        for g in ("a", "b"):
            specs = m87.named_specs(g, fake_reps(g))
            self.assertEqual([sp["name"] for sp in specs],
                             [m87.named_name(r[0], r[1], r[2]) for r in m87.named_rows(g)])
            self.assertTrue(all(bool(sp.get("lemma93")) == (sp["rank_x1"] == 0) for sp in specs))
            self.assertTrue(all(sp["name"].startswith("r3l_") == (sp["rank_x1"] == 0)
                                for sp in specs))
            self.assertEqual([sp["parent"] for sp in specs],
                             [n for n in m87.NAMED_CLASSES[g] for r in rows if r[0] == n])

    def test_plan(self):
        for g in ("a", "b"):
            reps = fake_reps(g)
            p = m69.plan(g, reps)
            named = [e for e in p if e[4]]
            tail = [e[0] for e in p if not e[4]]
            gates = [m87.GATE[n] for n in m87.TAILS[g]]
            self.assertEqual(len(named), 2 * m87.NAMED_COUNT[g])
            self.assertTrue(all(e[4] for e in p[:len(named)]))
            self.assertEqual([e[1] for e in named[:2]], ["cadical", "xor"])
            self.assertEqual(named[1][3], "open")
            self.assertEqual(named[0][2], m69.NAMED_CAP)
            self.assertEqual(len(tail), sum(m69.planned(n) for n in m87.TAILS[g]))
            self.assertEqual(len(tail), sum(gt["orbits"] for gt in gates))
            self.assertEqual(sum(1 for s in tail if s.get("lemma93")),
                             sum(gt["by_rank"]["0"] for gt in gates))
            self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
            self.assertEqual(len({s["name"] for s in tail}), len(tail))
            self.assertFalse({e[0]["name"] for e in named} & {s["name"] for s in tail})
            self.assertEqual([s["parent"] for s in tail],
                             [n for n, gt in zip(m87.TAILS[g], gates) for _ in range(gt["orbits"])])
            self.assertEqual(tail[0]["parent"], m87.TAILS[g][0])
            self.assertEqual(tail[0]["rank_x1"], 2)
            self.assertEqual(tail[-1]["rank_x1"], 0)

    def test_units(self):
        for g in ("a", "b"):
            specs = m87.named_specs(g, fake_reps(g))
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
        self.assertEqual(sum(1 for s in m87.named_specs("a", fake_reps("a"))
                             if not s.get("lemma93")), 1)

    def write_run(self, d, group, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = [e for e in m69.plan(group, reps) if e[1] == "cadical"]
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        for g in ("a", "b"):
            reps = fake_reps(g)
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps)
                out = m87.grade(g, d)
                self.assertEqual(out["b6_closed"],
                                 list(m87.TAILS[g]) + list(m87.NAMED_CLASSES[g]))
                self.assertFalse(out["any_sat_7"])
                self.assertNotIn("o020", out)
                self.assertNotIn("b5_closed", out)
                self.assertEqual(out["named_unsat"], m87.NAMED_COUNT[g])
                self.assertEqual(out["named_open"], [])
                self.assertEqual(out["named_max_unsat_wall"], 1.0)
                self.assertEqual(out["named_unsat_by_arm"],
                                 {"cadical": m87.NAMED_COUNT[g], "xor": 0})
                self.assertTrue(all(c["empty"] for c in out["named_classes"].values()))
                self.assertIn("SUMMARY grade", m87.summary_line(out))
            with tempfile.TemporaryDirectory() as d:
                self.write_run(d, g, reps, skip=1)
                out = m87.grade(g, d)
                last = m87.TAILS[g][-1]
                self.assertFalse(out["classes"][last]["empty"])
                self.assertEqual(out["classes"][last]["skipped"], 1)
                self.assertTrue(out["classes"][m87.TAILS[g][0]]["empty"])
            with tempfile.TemporaryDirectory() as d:
                first = m87.named_specs(g, reps)[0]
                self.write_run(d, g, reps)
                os.remove(os.path.join(d, m.tag_of(first, "cadical") + ".json"))
                out = m87.grade(g, d)
                c = out["named_classes"][first["parent"]]
                self.assertFalse(c["empty"])
                self.assertEqual(c["unsat"], m87.BEFORE[first["parent"]][0] - 1)
                self.assertEqual(c["open"], [first["name"]])
                self.assertEqual(out["named_open"], [first["name"]])
                self.assertNotIn(first["parent"], out["b6_closed"])
                self.assertIn("SUMMARY grade", m87.summary_line(out))


if __name__ == "__main__":
    unittest.main()
