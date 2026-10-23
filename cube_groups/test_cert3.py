# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert3.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert3
import m57 as m
import m69
import m92


def fake_reps(group):
    """m66-shaped roots of the group's class: rank 2 except at m92's rows, which carry their
    values."""
    name = cert3.GROUPS[group]
    reps = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
            for i in range(m92.NAMED_GATE[name]["orbits"])]
    for _, k, rk, index, size, a1 in cert3.rows(group):
        reps[k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert3(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert3.groups_ok())
        self.assertEqual([len(cert3.rows(g)) for g in ("a", "b")], [25, 20])
        self.assertEqual(sorted(cert3.M92_PROBES), ["a", "b"])
        self.assertEqual(sorted(cert3.M92_PROBES["b"]), ["l", "s"])

    def test_specs(self):
        for g in ("a", "b"):
            specs = cert3.group_specs(g, fake_reps(g))
            self.assertTrue(cert3.specs_ok(g, specs))
            self.assertFalse(cert3.specs_ok(g, specs[:-1]))
            self.assertEqual(sum(bool(sp.get("lemma93")) for sp in specs),
                             m92.NAMED_RANKS[g][0])
        a = cert3.group_specs("a", fake_reps("a"))
        self.assertEqual((a[0]["name"], a[-1]["name"]),
                         ("r3l_t7_B6_o003_c000_a0042", "r3l_t7_B6_o003_c000_a1559"))
        bb = cert3.group_specs("b", fake_reps("b"))
        self.assertEqual([sp["name"] for sp in bb if not sp.get("lemma93")],
                         ["r3s_t7_B6_o005_c000_a0335", "r3s_t7_B6_o005_c000_a0463"])
        bad = fake_reps("b")
        bad[1906] = dict(bad[1906], a1=bad[1906]["a1"] ^ 2)
        self.assertFalse(cert3.specs_ok("b", cert3.group_specs("b", bad)))

    def test_grade(self):
        specs = cert3.group_specs("b", fake_reps("b"))
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert3.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 1.0},
                       "drat": {"verified": True, "seconds": 2.0}, "proof_bytes": 100 + i,
                       "cnf_sha256": "0" * 64}
                with open(os.path.join(d, f"cert3_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert3.grade("b", d)
            self.assertEqual(out["instances"], 20)
            self.assertEqual(out["verified"], 19)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["counts"], {"VERIFIED": 19, "MISSING": 1})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (19.0, 38.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 118])
            self.assertEqual(len(out["rows"]), 20)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert3.summary_line(out))


if __name__ == "__main__":
    unittest.main()
