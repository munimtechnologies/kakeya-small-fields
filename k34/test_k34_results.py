# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Re-checks committed k34 results (k34/results/*.json):

* progress-q4-T28.json: q = 4, T = 28; the orbit counts match a fresh orbit computation; every
  finished item is complete; every reported set passes the independent checker and has the
  stated size; leaf_min_overall is the minimum of the item minima; and if the file says the
  search is complete, then nothing is pending and, for every orbit representative S0 of every
  size r <= 6, the finished prefixes of S0 cover the whole search tree.
* controls.json: the F_3^3 controls reproduced K(3, 3) = 13.
* control-q4-T29.json (if present): any reported set passes the checker."""
import json
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import slices, verify
except ImportError:  # pragma: no cover
    import slices
    import verify

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, "results")


def _load(name):
    path = os.path.join(RES, name)
    if not os.path.exists(path):
        return None
    with open(path) as fh:
        return json.load(fh)


class TestK34Results(unittest.TestCase):
    def test_progress(self):
        prog = _load("progress-q4-T28.json")
        if prog is None:
            self.skipTest("no progress file in this checkout")
        self.assertEqual(prog["q"], 4)
        self.assertEqual(prog["T"], 28)
        geo = slices.Geo(4)
        reps = {}
        for r in range(1, 7):
            orbs = slices.orbits(geo, r)
            self.assertEqual(prog["orbit_counts"][str(r)], len(orbs))
            for rep, _sz in orbs:
                reps[tuple(rep)] = r
        mins = []
        for d in prog["done"]:
            self.assertTrue(d["complete"])
            self.assertIn(tuple(d["S0"]), reps)
            for s in d["solutions"]:
                self.assertEqual(len(s["points"]), s["size"])
                self.assertLess(s["size"], 28)
                self.assertTrue(verify.is_kakeya3(s["points"], 4)[0])
            if d["leaf_min"] is not None:
                mins.append(d["leaf_min"])
        self.assertEqual(prog.get("leaf_min_overall"), min(mins) if mins else None)
        if prog.get("complete"):
            self.assertEqual(prog["pending"], [])
            by_rep = {}
            for d in prog["done"]:
                by_rep.setdefault(tuple(d["S0"]), set()).add(tuple(d["prefix"]))
            for rep, r in reps.items():
                self.assertIn(rep, by_rep, rep)
                self.assertTrue(slices.covered(by_rep[rep], r), rep)

    def test_controls(self):
        c = _load("controls.json")
        if c is None:
            self.skipTest("no controls file in this checkout")
        self.assertEqual(c["f3"]["T13"]["solutions"], 0)
        self.assertEqual(c["f3"]["T14"]["leaf_min"], 13)
        ex = c["f3"]["T14"]["example"]
        self.assertEqual(len(ex), 13)
        self.assertTrue(verify.is_kakeya3(ex, 3)[0])
        self.assertEqual(c["kss"]["leaf_value"], 28)

    def test_positive_control(self):
        c = _load("control-q4-T29.json")
        if c is None:
            self.skipTest("no positive control in this checkout")
        for s in c["record"].get("solutions", []):
            self.assertEqual(len(s["points"]), s["size"])
            self.assertTrue(verify.is_kakeya3(s["points"], 4)[0])


if __name__ == "__main__":
    unittest.main()
