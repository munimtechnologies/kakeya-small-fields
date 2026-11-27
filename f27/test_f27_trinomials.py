# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""f27/TRINOMIALS.md: no map P(x) = c1 x^e1 + c2 x^e2 + c3 x^e3 of F_27 (at most three terms,
exponents 1..26, coefficients in F_27, constants free) has S(P) > 162.  So no F_27-polynomial
with at most three terms beats the Kakeya growth base 3/2^(2/3) at block length 3.

The scan covers every exponent set of size 1, 2 or 3 and every nonzero coefficient vector, up
to conjugation by multiplication by mu in F_27^* (which only rescales the first coefficient
whose exponent is not 1; test_f27_controls.py checks this and the coset cover).  Every score
within 1e-6 of 162 is decided exactly with integers (product of c^c against 2^162)."""
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


class TestTrinomials(unittest.TestCase):
    def test_no_trinomial_of_f27_beats_162(self):
        st = F.sweep_poly(workers=8)
        msg = F.describe(st)
        self.assertFalse(st["beats"], "BEATS 162: " + repr(st["beats"][:2]) + " || " + msg)
        self.assertEqual(st["maps"], F.expected_poly_count(), "COUNT || " + msg)
        self.assertLessEqual(st["max"], 162 + 1e-6, msg)
        self.assertGreater(st["max"], 100, msg)


if __name__ == "__main__":
    unittest.main()
