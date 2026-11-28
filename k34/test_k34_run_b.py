# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Gate run B: continues the resumable search for Kakeya sets of F_4^3 below 28 points (420 s).
Passes when it runs without error and any set it reports passes the independent checker."""
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import gaterun, verify
except ImportError:  # pragma: no cover
    import gaterun
    import verify


class TestK34RunB(unittest.TestCase):
    def test_run(self):
        prog = gaterun.main_search(420, "run-b")
        for d in prog["done"]:
            for s in d["solutions"]:
                self.assertTrue(verify.is_kakeya3(s["points"], 4)[0])
                self.assertEqual(len(s["points"]), s["size"])


if __name__ == "__main__":
    unittest.main()
