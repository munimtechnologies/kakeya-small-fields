# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""f27/POWERLINEAR.md: for every F_3-linear map L of F_27 (all 3^9 of them, singular ones
included) and every exponent e in 2..26 other than 3 and 9, neither P = L(x^e) nor
P = c x^e + L(x) (c in F_27^*) has S(P) > 162.  So no linear image of a power map, and no
power map plus a linear map, beats the Kakeya growth base 3/2^(2/3) at block length 3.

For c x^e + L, conjugation by multiplication by mu sends (c, L) to (c mu^(e-1), mu^-1 L mu),
and L runs over all linear maps, so c is taken from the coset representatives REPS[e]."""
import math
import os
import sys
import unittest

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

try:
    from . import f27scan as F
except ImportError:  # pragma: no cover
    import f27scan as F


class TestPowerLinear(unittest.TestCase):
    def test_no_power_linear_map_beats_162(self):
        res = F.sweep_linear(workers=8)
        exp = F.expected_linear_counts()
        msg = " | ".join("%s: %s" % (k, F.describe(res[k])) for k in ("lin", "lpow", "plus"))
        for k in ("lin", "lpow", "plus"):
            self.assertFalse(res[k]["beats"], "BEATS 162 in %s: %r || %s"
                             % (k, res[k]["beats"][:2], msg))
        for k in ("lin", "lpow", "plus"):
            self.assertEqual(res[k]["maps"], exp[k], "COUNT %s || %s" % (k, msg))
            self.assertLessEqual(res[k]["max"], 162 + 1e-6, msg)
        self.assertAlmostEqual(res["lin"]["max"], 81 * math.log2(3), places=9, msg=msg)


if __name__ == "__main__":
    unittest.main()
