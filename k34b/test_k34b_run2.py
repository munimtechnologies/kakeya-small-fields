# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""k34b, the independent second search for Kakeya sets of F_4^3 below 28 points: session b-run-2.
It resumes the saved progress file of session b-run-1 (same folder, same file) for about 400 s and
checks every reported set with k34b's own Kakeya checker. Results are committed later behind a
checker test (test_k34b_complete.py)."""
import os
import sys
import time
import unittest

_HERE = os.path.dirname(os.path.abspath(__file__))
if _HERE not in sys.path:
    sys.path.insert(0, _HERE)

import indep  # noqa: E402

OUT = os.environ.get("K34B_OUT") or r"E:\MV2-Pursuit\work\20261128T072812Z-mathematics\gate-out\k34b"
LABEL = "b-run-2"
BUDGET = 400.0
T_START = time.time()


class TestK34bSession(unittest.TestCase):
    def test_session(self):
        self.assertTrue(os.path.exists(os.path.join(OUT, "indep-q4-T28.json")),
                        "progress file of b-run-1 missing; refusing to restart from scratch")
        budget = max(20.0, BUDGET - (time.time() - T_START))
        st = indep.queue(4, 28, OUT, budget, LABEL, item_cap=300.0)
        self.assertEqual((st["q"], st["T"]), (4, 28))
        for x in st["finished"]:
            for s in x["solutions"]:
                self.assertTrue(indep.kakeya_ok(s["points"], 4))


if __name__ == "__main__":
    unittest.main()
