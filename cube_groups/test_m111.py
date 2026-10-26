# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m111.py (job m111, notes/a103.md). Needs m42.py, sat_aniso.py and m100.py to
m106.py and m110.py next to it. pi(R) and the invariant subspaces are checked on matrices worked out
by hand, S against m99's d and Im A_u for all 68 classes, and the sampling and grading on small
tables worked out by hand."""
import tempfile
import unittest

import m100
import m102
import m103
import m104
import m111
import sat_aniso as sa

Q01 = frozenset({0, 1, 2, 3})


class TestLinearAlgebra(unittest.TestCase):
    def test_preserves_by_hand(self):
        # E_01 sends e_1 to e_0 and e_0 to 0: span(e_0, e_1) is invariant
        m = sa.entries(3, [(0, 1)])
        self.assertTrue(m111.preserves(m103.space_of(m102.case_t2(m)), Q01))
        # E_20 sends e_0 to e_2: span(e_0, e_1) is not invariant, span(e_2) is (E_20 e_2 = 0)
        m = sa.entries(3, [(2, 0)])
        sp = m103.space_of(m102.case_t2(m))
        self.assertFalse(m111.preserves(sp, Q01))
        self.assertTrue(m111.preserves(sp, frozenset({0, 4})))

    def test_row2_rule_on_all_t2(self):
        # span(I, M) leaves span(e_0, e_1) invariant iff M e_0 and M e_1 have no e_2 component,
        # i.e. entries (2, 0) and (2, 1) (bits 6 and 7) are zero
        for m in range(512):
            case = m102.case_t2(m)
            self.assertEqual(m111.preserves(m103.space_of(case), Q01), (m >> 6) & 3 == 0, m)
            self.assertEqual(m111.row2_rule(case), (m >> 6) & 3 == 0, m)

    def test_pi_r_by_hand(self):
        # Im A_u of m99 (echelon bases): o007 (64, 32, 1), o010 (64, 33, 2), o003 (32, 2, 1),
        # o000 (4, 2, 1), o011 (128, 64, 32); pi keeps bits 5..7
        self.assertEqual(m111.pi_r(m100.spec_of(7, 0)), Q01)
        self.assertEqual(m111.pi_r(m100.spec_of(10, 0)), Q01)
        self.assertEqual(m111.pi_r(m100.spec_of(3, 0)), frozenset({0, 1}))
        self.assertEqual(m111.pi_r(m100.spec_of(0, 0)), frozenset({0}))
        self.assertEqual(m111.pi_r(m100.spec_of(11, 0)), frozenset(range(8)))

    def test_s_against_m99(self):
        specs = m111.all_specs()
        self.assertEqual(len(specs), 68)
        for s in specs:
            self.assertEqual(len(m111.ker_s(s)), 2 ** s["dmeet"], s["name"])
            self.assertEqual(m111.im_s(s), m111.pi_r(s), s["name"])

    def test_level_masks(self):
        spec = m100.spec_of(7, 0)
        sizes = [len(m111.level_masks(spec, lv)) for lv in ("n", "in4", "out3")]
        self.assertEqual(sizes, [15, 255, 127])
        self.assertEqual(set(m111.level_masks(spec, "out3")),
                         set(m104.w_masks([0, 1, 2, 3, 8, 9, 10])))
        self.assertEqual(set(m111.level_masks(spec, "in4")), set(m104.w_masks(range(8))))
        # the control: M = J (the all-ones matrix, 511) in o000_c000
        cspec, ccase = m111.control_case()
        self.assertEqual(m102.inst_name(cspec, ccase), m111.CONTROL)
        self.assertEqual(ccase["maps"], [0, 511])


class TestTables(unittest.TestCase):
    def test_sample(self):
        names = ["r3b_t8_B7_o009_c000_t2_m012", "r3b_t8_B7_o007_c001_t2_m012",
                 "r3b_t8_B7_o007_c000_t3_m004_034", "r3b_t8_B7_o008_c003_t2_m092"]
        self.assertEqual(m111.sample(names), ["r3b_t8_B7_o007_c001_t2_m012",
                                              "r3b_t8_B7_o008_c003_t2_m092",
                                              "r3b_t8_B7_o007_c000_t3_m004_034"])
        self.assertEqual(m111.shard_sample("b", names), ["r3b_t8_B7_o007_c001_t2_m012",
                                                         "r3b_t8_B7_o007_c000_t3_m004_034"])
        self.assertEqual(m111.shard_sample("c", names), ["r3b_t8_B7_o008_c003_t2_m092"])

    def test_m110_parts(self):
        with tempfile.TemporaryDirectory() as d:
            m111.save(d, "m110a_grade.json", {"cases": {"x": {"n": "UNSAT"}}})
            self.assertIsNone(m111.m110_parts("ab", d))
            m111.save(d, "m110b_grade.json", {"cases": {"y": {"n": "SAT", "sweep": "UNKNOWN"}}})
            parts = m111.m110_parts("ab", d)
            self.assertEqual(m111.finals(parts), {"x": "UNSAT", "y": "UNKNOWN"})

    def test_grade_rows(self):
        def row(x, part, status, **kw):
            r = {"instance": x, "tag": f"{x}_{part.split()[-1]}", "part": part, "status": status}
            r.update(kw)
            return r

        clean = {"anisotropic": False}
        rows = [row("c", "control n", "SAT", verified=True, check=clean),
                row("c", "control in4", "UNKNOWN"), row("c", "control out3", "UNSAT"),
                row("x1", "in4", "UNSAT"), row("x1", "out3", "UNKNOWN"),
                row("x2", "in4", "UNKNOWN"), row("x2", "out3", "UNKNOWN"),
                row("x2", "sweep", "UNKNOWN"),
                row("x3", "in4", "SAT", verified=True, check=clean)]
        skipped = ["x3_out3", "x3_sweep"]
        g, out = m111.grade_rows(rows, skipped, ["x1", "x2", "x3"])
        self.assertTrue(all(g.values()), g)
        self.assertIn("verified_x3_in4", g)
        self.assertEqual(out["decided"], ["x1"])
        self.assertEqual(out["open"], ["x2", "x3"])
        self.assertEqual(out["by_level"], {"in4": {"UNSAT": 1, "UNKNOWN": 1, "SAT": 1},
                                           "out3": {"UNKNOWN": 2}, "sweep": {"UNKNOWN": 1}})
        self.assertEqual(out["full_models"], [])
        # a sweep after an UNSAT level breaks the rule; SAT there contradicts the UNSAT level, and a
        # model anisotropic on all of V is flagged
        rows.append(row("x1", "sweep", "SAT", verified=True, check={"anisotropic": True}))
        g, out = m111.grade_rows(rows, skipped, ["x1", "x2", "x3"])
        self.assertFalse(g["sweep_rule"])
        self.assertFalse(g["consistent"])
        self.assertEqual(out["full_models"], ["x1_sweep"])
        # no SAT control at "n"
        g, _ = m111.grade_rows(rows[1:], skipped, ["x1", "x2", "x3"])
        self.assertFalse(g["control_n_sat"])


if __name__ == "__main__":
    unittest.main()
