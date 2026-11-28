# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Re-checks committed kq results (kq/results/kq-<q>-<n>[-<tag>].json): every reported set
passes the independent checker and has the stated size; a reported dual bound never exceeds
the size of that run's own set; and, across all files for the same (q, n), every optimum that
an integer program reports (A or B with status 0, or min(C1, C2) when both finished) equals the
smallest set reported anywhere.  Files not in this checkout are skipped."""
import glob
import json
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import check
except ImportError:  # pragma: no cover
    import check

HERE = os.path.dirname(os.path.abspath(__file__))


class TestKQResults(unittest.TestCase):
    def test_all(self):
        files = sorted(glob.glob(os.path.join(HERE, "results", "kq-*.json")))
        if not files:
            self.skipTest("no kq results in this checkout")
        sizes, optima = {}, {}
        for path in files:
            with open(path) as fh:
                rep = json.load(fh)
            n, q = rep["n"], rep["q"]
            key = (q, n)
            self.assertTrue(rep["complete"], path)
            ls = rep["local_search"]
            self.assertEqual(len(ls["set"]), ls["best"])
            self.assertTrue(check.is_kakeya(ls["set"], n, q)[0], path)
            sizes.setdefault(key, []).append(ls["best"])
            milp = rep.get("milp") or {}
            for form, r in milp.items():
                if r.get("set") is not None:
                    self.assertEqual(len(r["set"]), r["best"])
                    self.assertTrue(check.is_kakeya(r["set"], n, q)[0], (path, form))
                    sizes[key].append(r["best"])
                if r.get("dual_bound") is not None and r.get("best") is not None:
                    self.assertLessEqual(r["dual_bound"], r["best"] + 1e-6, (path, form))
                if r.get("status") == 0 and form in ("A", "B"):
                    optima.setdefault(key, []).append(r["best"])
            if "C1" in milp and "C2" in milp and all(
                    milp[f].get("status") in (0, 2) for f in ("C1", "C2")):
                vals = [milp[f]["best"] for f in ("C1", "C2") if milp[f].get("status") == 0]
                self.assertTrue(vals, path)
                optima.setdefault(key, []).append(min(vals))
        for key, opts in optima.items():
            for o in opts:
                self.assertEqual(o, min(sizes[key]), key)


if __name__ == "__main__":
    unittest.main()
