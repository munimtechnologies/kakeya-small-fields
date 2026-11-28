# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Passes only if the committed run of the independent second search (k34b/indep.py) is COMPLETE
and found no Kakeya set of F_4^3 with 27 or fewer points: nothing left to do, no reported set,
every finished item complete with no leaf below 28, and for every orbit representative S0 of
every size r <= 6 (recomputed here from the full group of 5760 maps) the finished branch prefixes
cover the whole search tree. It also re-checks the saved controls (no 12-point set over F_3, a
13-point one found and accepted by the checker; the F_4 positive control's 28-point set accepted)
and the 28-point Kopparty-Saraf-Sudan set. With k34/ this is the second, independently written
computer route to K(3, 4) = 28."""
import json
import os
import sys
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import indep  # noqa: E402

PATH = os.path.join(_HERE, "results", "indep-q4-T28.json")
CTRL = os.path.join(_HERE, "results", "controls-b.json")


class TestK34bComplete(unittest.TestCase):
    def test_complete_and_empty(self):
        self.assertTrue(os.path.exists(PATH), "no results file")
        with open(PATH) as fh:
            st = json.load(fh)
        self.assertEqual((st["q"], st["T"], st["group_order"]), (4, 28, 5760))
        self.assertTrue(st["complete"])
        self.assertEqual(st["todo"], [])
        self.assertEqual(st["sets_below_T"], 0)
        P = indep.Plane(4)
        G = P.group()
        self.assertEqual(len(G), 5760)
        reps = {}
        for r in range(1, 7):
            for S0, _sz in indep.orbit_reps(P, r, G):
                reps[tuple(S0)] = r
        self.assertEqual(len(reps), 21)
        by_rep = {}
        for x in st["finished"]:
            self.assertTrue(x["complete"])
            self.assertEqual(x["T"], 28)
            self.assertEqual(x["solutions"], [])
            if x["leaf_min"] is not None:
                self.assertGreaterEqual(x["leaf_min"], 28)
            by_rep.setdefault(tuple(x["S0"]), set()).add(tuple(x["prefix"]))
        for rep, r in reps.items():
            self.assertIn(rep, by_rep, rep)
            self.assertTrue(indep.tree_covered(by_rep[rep], r), rep)
        kss = indep.kss_q4()
        self.assertEqual(len(kss), 28)
        self.assertTrue(indep.kakeya_ok(kss, 4))

    def test_controls(self):
        with open(CTRL) as fh:
            c = json.load(fh)
        self.assertEqual({int(k): v for k, v in c["orbit_counts_q4"].items()},
                         {1: 1, 2: 1, 3: 2, 4: 4, 5: 5, 6: 8})
        self.assertEqual(c["f3"]["T13_sets"], 0)
        self.assertEqual(c["f3"]["T14_leaf_min"], 13)
        ex = c["f3"]["T14_example"]
        self.assertEqual(len(set(map(tuple, ex))), 13)
        self.assertTrue(indep.kakeya_ok(ex, 3))
        pc = c["q4_positive_control"]["points"]
        self.assertEqual(len(set(map(tuple, pc))), 28)
        self.assertTrue(indep.kakeya_ok(pc, 4))


if __name__ == "__main__":
    unittest.main()
