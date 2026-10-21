# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m64.py. Hand counts are not tested here; the check part grades them."""
import json
import os
import tempfile
import unittest

import m57 as m
import m58
import m64


class TestM64(unittest.TestCase):
    def test_installed(self):
        m64.install()
        self.assertIs(m.build_plain, m64.build_plain_sweep)

    def test_specs(self):
        a, b = m64.specs("a"), m64.specs("b")
        self.assertEqual(len(a), len(m58.open_b6()))
        self.assertEqual(len(b), len(m64.B5_OPEN))
        for sp in a + b:
            self.assertTrue(sp["sweep0"])
            self.assertTrue(sp["name"].startswith("r3z_t7_B"))
            self.assertTrue(sp["parent"].startswith("r3b_t7_B"))
        self.assertTrue(all(sp["p"] == 6 for sp in a) and all(sp["p"] == 5 for sp in b))
        self.assertTrue(all(au for au in m64.b5_open().values()))

    def test_units(self):
        for group, kd in (("a", 3), ("b", 4)):
            sp = m64.specs(group)[0]
            self.assertEqual(m64.sweep_units(sp), 7 * 3 * (kd - 1))
            base = dict(sp)
            del base["sweep0"]
            c0, _, h0, u0 = m.build(base, "cadical")
            c1, names, h1, u1 = m.build(sp, "cadical")
            extra = c1.clauses[len(c0.clauses):]
            self.assertEqual(c1.clauses[:len(c0.clauses)], c0.clauses)
            self.assertEqual(len(extra), m64.sweep_units(sp))
            self.assertEqual((u0, u1, h0), (0, len(extra), h1))
            want = {names[0][i][r][c] for i in range(1, kd) for r in range(7)
                    for c in m64.x1_cols(sp)}
            self.assertEqual({-cl[0] for cl in extra}, want)
            self.assertTrue(m.units_consistent(c1))

    def test_plan_and_grade(self):
        self.assertEqual(len(m64.plan("a")), len(m58.open_b6()))
        self.assertEqual(len(m64.plan("b")), 2 * len(m64.B5_OPEN))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            for spec, arm, _, _ in m64.plan("b"):
                if arm == "cadical":
                    with open(os.path.join(d, m.tag_of(spec, arm) + ".json"), "w") as f:
                        json.dump({"status": "UNSAT", "wall_seconds": 1.0}, f)
            out = m64.grade("b", d)
            self.assertEqual(sorted(out["sweep_unsat"]), sorted(m64.B5_OPEN))
            self.assertFalse(out["any_sat_7"])


if __name__ == "__main__":
    unittest.main()
