# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for cert2.py that need neither CaDiCaL nor drat-trim; the check part runs cert1's
controls with both programs."""
import json
import os
import tempfile
import unittest

import cert1
import cert2
import m57 as m
import m69
import m90


def fake_reps():
    """m66-shaped roots of the class: rank 2 except at m90's re-runs, which carry their rows."""
    reps = [{"index": i, "cols": [0] * 7, "a1": 0, "rank_x1": 2, "size": 1}
            for i in range(m90.NAMED_GATE[cert2.NAME]["orbits"])]
    for _, k, rk, index, size, a1 in cert1.rerun_rows().values():
        reps[k] = {"index": index, "cols": [0] * 7, "a1": a1, "rank_x1": rk, "size": size}
    return reps


class TestCert2(unittest.TestCase):
    def test_installed(self):
        self.assertIs(m.build_plain, m69.build_plain69)

    def test_groups(self):
        self.assertTrue(cert2.groups_ok())
        self.assertEqual(len(cert2.ks("a")) + len(cert2.ks("b")), 1961)
        self.assertEqual((cert2.ks("a")[-1], cert2.ks("b")[0], cert2.ks("b")[-1]), (980, 981, 1960))
        sha = cert2.cert1_sha()
        self.assertEqual(len(sha), 99)
        self.assertTrue(all(len(v) == 64 and int(v, 16) >= 0 for v in sha.values()))
        self.assertEqual(len(set(sha.values())), 99)

    def test_specs(self):
        reps = fake_reps()
        for g in ("a", "b"):
            specs = cert2.group_specs(g, reps)
            self.assertTrue(cert2.specs_ok(g, specs))
            self.assertFalse(cert2.specs_ok(g, specs[:-1]))
        a = cert2.group_specs("a", reps)
        self.assertEqual(a[60]["name"], "r3s_t7_B6_o005_c003_a0060")
        self.assertEqual(a[240]["name"], "r3l_t7_B6_o005_c003_a0240")
        bb = cert2.group_specs("b", reps)
        self.assertEqual(bb[-1]["name"], "r3l_t7_B6_o005_c003_a1960")
        bad = fake_reps()
        bad[1960] = dict(bad[1960], a1=bad[1960]["a1"] ^ 2)
        self.assertFalse(cert2.specs_ok("b", cert2.group_specs("b", bad)))
        self.assertTrue(cert2.specs_ok("a", cert2.group_specs("a", bad)))

    def test_grade(self):
        specs = cert2.group_specs("b", fake_reps())
        sha = cert2.cert1_sha()
        with tempfile.TemporaryDirectory() as d:
            with open(os.path.join(d, "check.json"), "w") as f:
                json.dump({"graded": {"x": True}}, f)
            with open(os.path.join(d, cert2.SPECS_FILE), "w") as f:
                json.dump(specs, f)
            for i, sp in enumerate(specs[1:]):
                k = int(sp["name"][-4:])
                row = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "VERIFIED",
                       "cadical": {"status": "UNSAT", "seconds": 1.0},
                       "drat": {"verified": True, "seconds": 2.0}, "proof_bytes": 100 + i}
                if k in sha:
                    row["cnf_sha256"] = "0" * 64 if k == 1000 else sha[k]
                with open(os.path.join(d, f"cert2_{sp['name']}.json"), "w") as f:
                    json.dump(row, f)
            out = cert2.grade("b", d)
            self.assertEqual(out["instances"], 980)
            self.assertEqual(out["verified"], 979)
            self.assertEqual(out["not_verified"], [specs[0]["name"]])
            self.assertEqual(out["counts"], {"VERIFIED": 979, "MISSING": 1})
            self.assertEqual((out["cadical_sum"], out["drat_sum"]), (979.0, 1958.0))
            self.assertEqual(out["largest_proof"], [specs[-1]["name"], 1078])
            self.assertEqual(out["sha_compared"], 49)
            self.assertEqual(out["sha_differ"], ["r3s_t7_B6_o005_c003_a1000"])
            self.assertEqual(len(out["reruns"]), 15)
            self.assertFalse(out["any_sat"])
            self.assertIn("SUMMARY grade group b", cert2.summary_line(out))


if __name__ == "__main__":
    unittest.main()
