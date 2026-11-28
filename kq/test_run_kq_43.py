# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Smallest Kakeya set in F_4^3: local search plus (with scipy) the symmetry-broken integer
program B of kq.py, with the whole slot.  Passes when the run completes and every reported set
passes the independent checker."""
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import runcase as R
except ImportError:  # pragma: no cover
    import runcase as R


class TestRunKQ43(unittest.TestCase):
    def test_f4_3(self):
        R.run_and_check(self, 3, 4, 530, forms=("B",), ls_share=0.08, tag="B")


if __name__ == "__main__":
    unittest.main()
