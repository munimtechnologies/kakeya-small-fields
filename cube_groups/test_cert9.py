# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert9.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert9
import m57 as m
import m69
import m82


def fake_reps(group):
    """m66-shaped roots of the group's classes: rank 2 except at m82's rows, which carry their
    values."""
    reps = {}
    for name in cert9.classes(group):
        reps[name] = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
                      for i in range(m82.NAMED_GATE[name]["orbits"])]
    for name, k, rk, index, size, a1 in cert9.rows(group):
        reps[name][k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert9(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert9.groups_ok())
        self.assertEqual([len(cert9.rows(g)) for g in ("a", "b")], [21, 21])
        self.assertEqual(cert9.classes("a"), ["r3b_t7_B6_o008_c000"])
        self.assertEqual(cert9.classes("b"), ["r3b_t7_B6_o008_c001", "r3b_t7_B6_o008_c003"])
        self.assertEqual(cert9.per_class("a"), {"r3b_t7_B6_o008_c000": 21})
        self.assertEqual(cert9.per_class("b"),
                         {"r3b_t7_B6_o008_c001": 7, "r3b_t7_B6_o008_c003": 14})
        self.assertEqual(sorted(cert9.M82_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert9.M82_PROBES["a"]), ["l", "s"])
        self.assertEqual(sorted(cert9.M82_PROBES["b"]), ["l"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert9.group_specs(g, fake_reps(g))
            self.assertTrue(cert9.specs_ok(g, specs))
            self.assertFalse(cert9.specs_ok(g, specs[:-1]))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             21 - m82.NAMED_RANK1[g])
        a = cert9.group_specs("a", fake_reps("a"))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o008_c000_a0028", "r3l_t7_B6_o008_c000_a2014"))
        self.assertEqual([sp["name"] for sp in a if not sp.get("lemma93")],
                         ["r3s_t7_B6_o008_c000_a0619", "r3s_t7_B6_o008_c000_a0658"])
        bb = cert9.group_specs("b", fake_reps("b"))
        self.assertTrue(all(sp.get("lemma93") for sp in bb))
        self.assertEqual((bb[0]["name"], bb[-1]["name"]),
                         ("r3l_t7_B6_o008_c001_a0016", "r3l_t7_B6_o008_c003_a1973"))
        bad = fake_reps("b")
        row = bad["r3b_t7_B6_o008_c003"][1973]
        bad["r3b_t7_B6_o008_c003"][1973] = dict(row, a1=row["a1"] ^ 2)
        self.assertFalse(cert9.specs_ok("b", cert9.group_specs("b", bad)))

    def test_grade(self):
        specs = cert9.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert9.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 5.0 if i == 3 else 1.0},
                       "drat": {"verified": True, "seconds": 50.0 if i == 4 else 2.0},
                       "proof_bytes": 100 + i, "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert9_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert9.grade("b", d)
            self.assertEqual(out["instances"], 21)
            self.assertEqual(out["verified"], 20)
            self.assertEqual(out["not_verified"], ["r3l_t7_B6_o008_c001_a0016"])
            self.assertEqual(out["counts"], {"VERIFIED": 20, "MISSING": 1})
            self.assertEqual(out["by_class"],
                             {"r3b_t7_B6_o008_c001": {"instances": 7, "verified": 6},
                              "r3b_t7_B6_o008_c003": {"instances": 14, "verified": 14}})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (24.0, 88.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 119])
            self.assertEqual(out["slowest"], [specs[4]["name"], 5.0, 2.0])
            self.assertEqual(len(out["rows"]), 21)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert9.summary_line(out))


if __name__ == "__main__":
    unittest.main()
