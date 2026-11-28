# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Passes only if the committed search for Kakeya sets of F_4^3 below 28 points is COMPLETE and
found nothing: nothing pending, no reported set, every finished item complete with no leaf below
28, and for every orbit representative S0 (recomputed here) of every size r <= 6 the finished
branch prefixes cover the whole search tree. Together with the 28-point Kopparty-Saraf-Sudan set
this gives K(3, 4) = 28 (computer-assisted; see PROOF.md)."""
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
PATH = os.path.join(HERE, "results", "progress-q4-T28.json")


class TestK34Complete(unittest.TestCase):
    def test_complete_and_empty(self):
        self.assertTrue(os.path.exists(PATH), "no progress file")
        with open(PATH) as fh:
            prog = json.load(fh)
        self.assertEqual((prog["q"], prog["T"]), (4, 28))
        self.assertTrue(prog["complete"])
        self.assertEqual(prog["pending"], [])
        self.assertEqual(prog["solutions_found"], 0)
        geo = slices.Geo(4)
        reps = {}
        for r in range(1, 7):
            for rep, _sz in slices.orbits(geo, r):
                reps[tuple(rep)] = r
        by_rep = {}
        for d in prog["done"]:
            self.assertTrue(d["complete"])
            self.assertEqual(d["solutions"], [])
            if d["leaf_min"] is not None:
                self.assertGreaterEqual(d["leaf_min"], 28)
            by_rep.setdefault(tuple(d["S0"]), set()).add(tuple(d["prefix"]))
        for rep, r in reps.items():
            self.assertIn(rep, by_rep, rep)
            self.assertTrue(slices.covered(by_rep[rep], r), rep)
        kss = verify.kss_set_q4()
        self.assertEqual(len(kss), 28)
        self.assertTrue(verify.is_kakeya3(kss, 4)[0])


if __name__ == "__main__":
    unittest.main()
