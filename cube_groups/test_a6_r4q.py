# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of a6_r4q.py (job m25). Pure Python: no SAT solver is needed."""
import json
import os
import tempfile
import unittest

import a6_r4q
import shape_c as sc
import shape_c2 as s2


class TestInstances(unittest.TestCase):
    def test_selfcheck(self):
        # Hand counts (notes/a12.md): 34 classes; C(M)-orbits on non-zero vectors 126 in all,
        # 124 without M = 0 and M = I; types 22, 22, 80; 149 instances, 146 kept.
        st = a6_r4q.selfcheck()
        self.assertTrue(all(st["graded"].values()), st["graded"])

    def test_todo(self):
        kept = a6_r4q.todo(6)
        ident = sc.identity(4)
        self.assertEqual(len(kept), 146)
        self.assertTrue(all(inst[0] not in (0, ident) for _, inst in kept))
        self.assertEqual(len({idx for idx, _ in kept}), 146)
        insts = s2.instances(6)
        self.assertTrue(all(insts[idx] == inst for idx, inst in kept))
        left = [inst for idx, inst in enumerate(insts) if idx not in {i for i, _ in kept}]
        self.assertEqual(sorted((M, typ) for M, _, typ, _ in left), [(0, "i"), (ident, "ii"),
                                                                     (ident, "ii")])
        self.assertEqual([len(a6_r4q.todo(t)) for t in (3, 4, 5)], [3, 13, 47])

    def test_round_robin(self):
        items = [(0, (7, 1, "i", 0)), (1, (7, 2, "iii", 0)), (2, (9, 1, "ii", 0)),
                 (3, (9, 1, "ii", 1)), (4, (9, 3, "iii", 0)), (5, (11, 1, "iii", 0))]
        self.assertEqual([idx for idx, _ in a6_r4q.round_robin(items)], [0, 2, 5, 1, 3, 4])
        self.assertEqual(a6_r4q.round_robin([]), [])
        rr = a6_r4q.round_robin(a6_r4q.todo(6))
        self.assertEqual(sorted(rr), sorted(a6_r4q.todo(6)))
        self.assertEqual(len({inst[0] for _, inst in rr[:32]}), 32)

    def test_child_cmd_round_trip(self):
        idx, inst = a6_r4q.todo(6)[0]
        cmd = a6_r4q.child_cmd(6, inst, "auto", "x.json")
        i = cmd.index("--inst")
        self.assertEqual(tuple(json.loads(cmd[i + 1])), inst)
        self.assertEqual(cmd[cmd.index("--t") + 1], "6")
        self.assertEqual(cmd[cmd.index("--part") + 1], "child")


class TestGrade(unittest.TestCase):
    def write(self, d, name, res):
        with open(os.path.join(d, name + ".json"), "w") as f:
            json.dump(res, f)

    def test_grade_synthetic(self):
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "selfcheck.json"), "w") as f:
                json.dump({"graded": {"all": True}}, f)
            for t in a6_r4q.CONTROLS:
                for idx, _ in a6_r4q.todo(t):
                    name = s2.instance_name(t, idx)
                    self.write(d, name, {"status": "UNSAT", "name": name, "t": t})
            five = a6_r4q.todo(5)
            n0 = s2.instance_name(5, five[0][0])
            n1 = s2.instance_name(5, five[1][0])
            self.write(d, n0, {"status": "UNSAT", "name": n0, "t": 5})
            self.write(d, n1, {"status": "UNKNOWN", "name": n1, "t": 5})
            idx6, inst6 = a6_r4q.todo(6)[0]
            n6 = s2.instance_name(6, idx6)
            self.write(d, n6, {"status": "UNKNOWN", "name": n6, "t": 6, "wall_seconds": 180.0})
            out = a6_r4q.grade(d)
            self.assertTrue(all(out["graded"].values()), out["graded"])
            self.assertEqual(len(out["graded"]), 1 + 3 + 13 + 1)
            self.assertEqual(out["ungraded"][n1], "UNKNOWN")
            self.assertEqual(len(out["ungraded"]), 46)
            self.assertEqual(out["counts"]["6"], {"UNKNOWN": 1, "missing": 145})
            self.assertEqual(out["counts"]["5"], {"UNKNOWN": 1, "UNSAT": 1, "missing": 45})
            self.assertEqual(out["by_type_6"][inst6[2]].get("UNKNOWN"), 1)
            self.assertEqual(out["decided_6"], [])
            self.assertFalse(out["all_unsat_6"])
            self.assertFalse(out["any_sat_6"])
            # a SAT answer at t = 5 contradicts Corollary 24 and fails the grade, as does an
            # unverified one
            self.write(d, n1, {"status": "SAT", "name": n1, "t": 5, "verified": False,
                               "facts": {"max_rank": 3}})
            out = a6_r4q.grade(d)
            self.assertFalse(out["graded"][n1])
            self.assertFalse(out["graded"][n1 + "_verified"])
            self.assertTrue(out["graded"][n1 + "_ranks"])
            # an UNSAT at t = 6 is reported, not graded
            self.write(d, n6, {"status": "UNSAT", "name": n6, "t": 6})
            out = a6_r4q.grade(d)
            self.assertNotIn(n6, out["graded"])
            self.assertEqual(out["decided_6"], [n6])

    def test_grade_missing(self):
        with tempfile.TemporaryDirectory() as d:
            out = a6_r4q.grade(d)
            self.assertEqual(out["ungraded"]["selfcheck"], "missing")
            self.assertEqual(out["counts"]["6"], {"missing": 146})
            self.assertEqual(out["counts"]["3"], {"missing": 3})


if __name__ == "__main__":
    unittest.main()
