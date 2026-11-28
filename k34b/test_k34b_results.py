# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Checks a committed (possibly partial) run of the independent second search k34b/indep.py:
well-formed file, every finished item complete with no reported set and no leaf below 28 unless a
set was reported (then the set must pass the checker), and the saved controls."""
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


class TestK34bResults(unittest.TestCase):
    def test_progress(self):
        with open(PATH) as fh:
            st = json.load(fh)
        self.assertEqual((st["q"], st["T"], st["group_order"]), (4, 28, 5760))
        self.assertEqual(st["complete"], not st["todo"])
        n = 0
        for x in st["finished"]:
            self.assertTrue(x["complete"])
            for s in x["solutions"]:
                n += 1
                self.assertTrue(indep.kakeya_ok(s["points"], 4))
                self.assertEqual(len(set(map(tuple, s["points"]))), s["size"])
            if not x["solutions"] and x["leaf_min"] is not None:
                self.assertGreaterEqual(x["leaf_min"], 28)
        self.assertEqual(n, st["sets_below_T"])

    def test_controls(self):
        with open(CTRL) as fh:
            c = json.load(fh)
        self.assertEqual(c["f3"]["T13_sets"], 0)
        self.assertTrue(indep.kakeya_ok(c["f3"]["T14_example"], 3))
        self.assertTrue(indep.kakeya_ok(c["q4_positive_control"]["points"], 4))


if __name__ == "__main__":
    unittest.main()
