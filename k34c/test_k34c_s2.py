# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""k34c phase 1, session s2: resumes the saved progress of s1 for about 420 s (returns at once
if nothing is pending; refuses to start from scratch) and re-checks the listed sets."""
import os
import sys
import time
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import classify  # noqa: E402
import indep  # noqa: E402

OUT = os.environ.get("K34C_OUT") or r"E:\MV2-Pursuit\work\20261128T130947Z-mathematics\gate-out\k34c"
LABEL = "c-run-2"
BUDGET = 420.0
T_START = time.time()


class TestK34cSession(unittest.TestCase):
    def test_session(self):
        path, _s = classify.paths(OUT)
        self.assertTrue(os.path.exists(path), "progress file of c-run-1 missing; refusing to restart")
        budget = max(20.0, BUDGET - (time.time() - T_START))
        st = classify.queue(OUT, budget, LABEL, item_cap=300.0)
        self.assertEqual((st["q"], st["T"], st["rmax"]), (4, 29, 6))
        if st["leaf_min"] is not None:
            self.assertGreaterEqual(st["leaf_min"], 28)
        sets = classify.load_sets(OUT)
        self.assertEqual(len(sets), st["n_sets"])
        for s in sets:
            self.assertEqual(bin(s).count("1"), 28)
        for s in sorted(sets)[-40:]:
            self.assertTrue(indep.kakeya_ok(classify.mask_points(s, 4), 4))


if __name__ == "__main__":
    unittest.main()
