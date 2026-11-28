# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Smallest Kakeya set in F_4^3, second formulation: the two-line normal forms C1 (second line
meets the x-axis) and C2 (second line skew to it) of kq.py, whose minimum is the optimum.
Passes when the run completes and every reported set passes the independent checker."""
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


class TestRunKQ43C(unittest.TestCase):
    def test_f4_3_c(self):
        R.run_and_check(self, 3, 4, 530, forms=("C1", "C2"), ls_share=0.03, tag="C")


if __name__ == "__main__":
    unittest.main()
