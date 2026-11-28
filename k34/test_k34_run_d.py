# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Gate run D (2026-11-28): continues the resumable search for Kakeya sets of F_4^3 below 28
points from the saved progress file (430 s). Only two items, both of size r = 6, were left after
run C; the item cap is raised so that an item is split only if it alone outlasts the entry.
Passes when it runs without error and any set it reports passes the independent checker."""
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import gaterun, slices, verify
except ImportError:  # pragma: no cover
    import gaterun
    import slices
    import verify


class TestK34RunD(unittest.TestCase):
    def test_run(self):
        prog = slices.run_queue(4, 28, gaterun.OUT, 430, "run-d", item_cap=425.0)
        for d in prog["done"]:
            for s in d["solutions"]:
                self.assertTrue(verify.is_kakeya3(s["points"], 4)[0])
                self.assertEqual(len(s["points"]), s["size"])


if __name__ == "__main__":
    unittest.main()
