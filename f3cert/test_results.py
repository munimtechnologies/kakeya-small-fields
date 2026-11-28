# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Re-checks the committed results of the f3cert gate runs (f3cert/results/<plan>/) with
f3cert/checkres.py: every exported bound is recomputed exactly from its listed rows and boxes,
the control certifies 1, and the verdict follows from the numbers.  Plans whose result folder
is not present in this checkout are skipped."""
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import checkres as C
except ImportError:  # pragma: no cover
    import checkres as C

HERE = os.path.dirname(os.path.abspath(__file__))


class TestResults(unittest.TestCase):
    def _plan(self, plan):
        d = os.path.join(HERE, "results", plan)
        if not os.path.isfile(os.path.join(d, "results.json")):
            self.skipTest("no results for " + plan)
        out = C.check(d)
        self.assertIn("verdict", out)

    def test_five(self):
        self._plan("five")

    def test_aug(self):
        self._plan("aug")

    def test_std(self):
        self._plan("std")


if __name__ == "__main__":
    unittest.main()
