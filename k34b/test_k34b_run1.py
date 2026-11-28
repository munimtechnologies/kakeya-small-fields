# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""k34b, the independent second search: controls, then the first session of its resumable search
for Kakeya sets of F_4^3 below 28 points (results in gate-out/k34b, committed later behind a
checker). Controls: group orders 432 and 5760, orbit sizes add up to the binomial coefficients,
the checker accepts F_4^3 minus a point and the 28-point KSS set and rejects a plane, the F_3
search reproduces K(3, 3) = 13, and the F_4 positive control reaches a 28-point set when asked
for sets below 29 on the orbit of the 2 x 2 grid."""
import json
import math
import os
import sys
import time
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import indep  # noqa: E402

OUT = os.environ.get("K34B_OUT") or r"E:\MV2-Pursuit\work\20261128T072812Z-mathematics\gate-out\k34b"
T_START = time.time()


class TestK34bRun1(unittest.TestCase):
    def test_all(self):
        res = {"made_with": "AI agents working in MV2's name; not checked by a human mathematician"}
        P3, P4 = indep.Plane(3), indep.Plane(4)
        G3, G4 = P3.group(), P4.group()
        self.assertEqual(len(G3), 432)
        self.assertEqual(len(G4), 5760)
        counts = {}
        for r in range(1, 7):
            reps = indep.orbit_reps(P4, r, G4)
            self.assertEqual(sum(s for _, s in reps), math.comb(16, r))
            counts[r] = len(reps)
        res["orbit_counts_q4"] = counts
        full = [[x, y, z] for x in range(4) for y in range(4) for z in range(4)]
        self.assertTrue(indep.kakeya_ok(full[1:], 4))
        self.assertFalse(indep.kakeya_ok([p for p in full if p[2] == 0], 4))
        kss = indep.kss_q4()
        self.assertEqual(len(kss), 28)
        self.assertTrue(indep.kakeya_ok(kss, 4))
        # F_3 control: K(3, 3) = 13
        a = indep.search_all(3, 13)
        self.assertEqual(sum(len(x["solutions"]) for x in a), 0)
        b = indep.search_all(3, 14)
        mins = [x["leaf_min"] for x in b if x["leaf_min"] is not None]
        self.assertEqual(min(mins), 13)
        sols = [s for x in b for s in x["solutions"]]
        self.assertTrue(sols)
        for s in sols:
            self.assertEqual(s["size"], s["value"])
            self.assertEqual(s["size"], 13)
            self.assertTrue(indep.kakeya_ok(s["points"], 3))
        res["f3"] = {"T13_sets": 0, "T14_leaf_min": 13, "T14_example": sols[0]["points"]}
        # F_4 positive control on the orbit of the 2 x 2 grid
        grid = tuple(sorted(P4.ix[p] for p in [(0, 0), (0, 1), (1, 0), (1, 1)]))
        rep = None
        for S0, _sz in indep.orbit_reps(P4, 4, G4):
            if grid in set(tuple(sorted(g[p] for p in S0)) for g in G4):
                rep = S0
        self.assertIsNotNone(rep)
        rec = indep.Search(P4, rep, 29, stop_first=True, keep=1).go()
        self.assertTrue(rec["solutions"])
        s = rec["solutions"][0]
        self.assertEqual(s["size"], 28)
        self.assertEqual(s["value"], 28)
        self.assertTrue(indep.kakeya_ok(s["points"], 4))
        res["q4_positive_control"] = {"rep": rep, "nodes": rec["nodes"], "size": 28,
                                      "points": s["points"]}
        os.makedirs(OUT, exist_ok=True)
        with open(os.path.join(OUT, "controls-b.json"), "w") as fh:
            json.dump(res, fh, indent=1)
        # first session of the main search
        budget = max(30.0, 330.0 - (time.time() - T_START))
        st = indep.queue(4, 28, OUT, budget, "b-run-1")
        for x in st["finished"]:
            for s in x["solutions"]:
                self.assertTrue(indep.kakeya_ok(s["points"], 4))


if __name__ == "__main__":
    unittest.main()
