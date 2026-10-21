# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m71.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m66
import m69
import m71


def fake_reps():
    """m66-shaped reps: the tails' ranks follow their GATE counts; the two named classes have roots
    of rank 2 except at the 21, which carry m69b's recorded index, map, rank and size."""
    reps = {}
    for name in m71.TAILS["a"]:
        by = m71.GATE[name]["by_rank"]
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": int(r), "size": 1}
                      for i, r in enumerate(r for r in "012" for _ in range(by[r]))]
    for name, gate in m71.NAMED_GATE.items():
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(gate["orbits"])]
    for name, k, rk, index, size, a1 in m71.OPEN_M69B:
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestM71(unittest.TestCase):
    def test_installed(self):
        m71.install()
        self.assertIs(m.build_plain, m69.build_plain69)
        self.assertEqual(m69.NAMED, {"a": (), "b": ()})
        self.assertIs(m69.TAILS, m71.TAILS)
        self.assertIs(m69.GATE, m71.GATE)
        self.assertIs(m69.SWEEP, m71.SWEEP)
        self.assertIs(m69.plan, m71.plan)
        self.assertEqual(m69.REPS_FILE, "m71_reps.json")

    def test_lists(self):
        cl = m66.classes()
        names = set(m71.TAILS["a"])
        self.assertEqual(m71.TAILS["b"], ())
        self.assertEqual(names, set(m71.GATE))
        self.assertEqual(names, set(m71.SWEEP))
        self.assertFalse(names & (set(m71.CLOSED_M69) | set(m71.SPLIT_ELSEWHERE)))
        both = names | set(m71.NAMED_GATE)
        self.assertFalse(both & (set(m58.CLOSED_KNOWN) | set(m69.CLOSED_M61B)))
        self.assertFalse(set(m71.NAMED_GATE) & set(m71.CLOSED_M69))
        for name in both:
            self.assertIn(name, cl)
            gate = m71.GATE.get(name) or m71.NAMED_GATE[name]
            self.assertEqual(sum(gate["by_rank"].values()), gate["orbits"])
            self.assertEqual(m58.HAND_D_PAIR[m66.pair_of(name)], gate["d"])
            self.assertEqual(m66.HAND_ORDER[name], gate["order"])
        self.assertFalse([n for n in names if m69.drop_rank0(n)])
        self.assertEqual(set(m71.NAMED_GATE), set(m71.M69B))

    def test_named(self):
        rows = m71.OPEN_M69B
        self.assertEqual(len(rows), 21)
        self.assertEqual(len({(r[0], r[1]) for r in rows}), 21)
        for name, (total, unsat) in m71.M69B.items():
            self.assertEqual(sum(r[0] == name for r in rows), total - unsat)
        self.assertEqual([r[2] for r in rows], sorted((r[2] for r in rows), reverse=True))
        for name, k, rk, index, size, a1 in rows:
            au, rb = m66.classes()[name], m69.r_of(name)
            mp = m66.Maps(rb)
            self.assertEqual(m69.rank_on(a1, m69.X1), rk)
            self.assertTrue(m69.admissible_b6(a1, au, rb, m71.NAMED_GATE[name]["d"]))
            self.assertEqual(mp.index(m66.cols_of_mask(a1)), index)
            self.assertEqual(mp.rank_x1(index), rk)
            self.assertLess(k, m71.NAMED_GATE[name]["orbits"])
        specs = m71.named_specs("a", fake_reps())
        self.assertEqual([sp["name"] for sp in specs],
                         [m71.named_name(r[0], r[1], r[2]) for r in rows])
        self.assertTrue(all(bool(sp.get("lemma93")) == (sp["rank_x1"] == 0) for sp in specs))
        self.assertEqual(m71.named_specs("b", fake_reps()), [])

    def test_plan(self):
        reps = fake_reps()
        p = m69.plan("a", reps)
        named = [e for e in p if e[4]]
        tail = [e[0] for e in p if not e[4]]
        self.assertEqual(len(named), 2 * 21)
        self.assertTrue(all(e[4] for e in p[:len(named)]))
        self.assertEqual([e[1] for e in named[:2]], ["cadical", "xor"])
        self.assertEqual(named[1][3], "open")
        self.assertEqual(len(tail), sum(m69.planned(n) for n in m71.TAILS["a"]))
        self.assertEqual(len(tail), 1021 + 1021)
        self.assertTrue(all(bool(s.get("lemma93")) == (s["rank_x1"] == 0) for s in tail))
        self.assertEqual(len({s["name"] for s in tail}), len(tail))
        self.assertFalse({e[0]["name"] for e in named} & {s["name"] for s in tail})
        self.assertEqual(tail[0]["parent"], m71.TAILS["a"][0])
        self.assertEqual(tail[0]["rank_x1"], 2)

    def test_units(self):
        specs = m71.named_specs("a", fake_reps())
        sp = next(s for s in specs if s.get("lemma93"))
        self.assertEqual(m69.lemma93_units(sp), 21)
        _, _, h, u = m.build(dict(sp), "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49 + 21))
        ok, _ = m69.probe93(sp)
        self.assertTrue(all(ok.values()))
        plain = next(s for s in specs if not s.get("lemma93"))
        _, _, h, u = m.build(dict(plain), "cadical")
        self.assertEqual((h, u), (m.HAND_HINTS["B6"], 49))

    def write_run(self, d, reps, skip=0):
        with open(os.path.join(d, "check.json"), "w") as f:
            json.dump({"graded": {"x": True}}, f)
        with open(os.path.join(d, m69.REPS_FILE), "w") as f:
            json.dump(reps, f)
        p = [e for e in m69.plan("a", reps) if e[1] == "cadical"]
        for spec, arm, _, _, _ in p[:len(p) - skip]:
            with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump({"status": "UNSAT", "wall_seconds": 1.0, "budget_seconds": 10.0}, f)

    def test_grade(self):
        reps = fake_reps()
        with tempfile.TemporaryDirectory() as d:
            self.write_run(d, reps)
            out = m71.grade("a", d)
            self.assertEqual(out["b6_closed"], list(m71.TAILS["a"]) + list(m71.M69B))
            self.assertFalse(out["any_sat_7"])
            self.assertNotIn("o020", out)
            self.assertNotIn("b5_closed", out)
            self.assertEqual(out["named_unsat"], 21)
            self.assertEqual(out["named_open"], [])
            self.assertEqual(out["named_max_unsat_wall"], 1.0)
            self.assertTrue(all(c["empty"] for c in out["named_classes"].values()))
            self.assertIn("SUMMARY grade", m71.summary_line(out))
        with tempfile.TemporaryDirectory() as d:
            self.write_run(d, reps, skip=1)
            out = m71.grade("a", d)
            last = m71.TAILS["a"][-1]
            self.assertFalse(out["classes"][last]["empty"])
            self.assertEqual(out["classes"][last]["skipped"], 1)
        with tempfile.TemporaryDirectory() as d:
            first = m71.named_specs("a", reps)[0]
            self.write_run(d, reps)
            os.remove(os.path.join(d, m.tag_of(first, "cadical") + ".json"))
            out = m71.grade("a", d)
            c = out["named_classes"][first["parent"]]
            self.assertFalse(c["empty"])
            self.assertEqual(c["unsat"], 586)
            self.assertEqual(c["open"], [first["name"]])
            self.assertEqual(out["named_open"], [first["name"]])
            self.assertNotIn(first["parent"], out["b6_closed"])
            self.assertIn("SUMMARY grade", m71.summary_line(out))


if __name__ == "__main__":
    unittest.main()
