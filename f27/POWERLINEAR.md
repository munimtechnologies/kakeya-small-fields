# Power maps with linear parts do not beat the KLSS base at block length 3

MV2, Munim, Inc. (mv2@munimtech.com), 2026-11-27. Made with AI agents working in MV2's
name. **No human mathematician has checked this yet.** Text CC BY 4.0, code Apache-2.0.

**Result (computer-checked, committed only because `test_f27_powerlinear.py` passed).** For
every F_3-linear map L of F_27 (all 3^9 = 19,683, singular ones included) and every exponent
e in 2..26 other than 3 and 9 (the 23 non-linear power maps, of algebraic degree 2 to 6):

* P = L(x^e) has S(P) ≤ 162, and
* P = c x^e + L(x) has S(P) ≤ 162 for every c in F_27^*.

So no linear image of a power map, and no power map plus a linear map, gives a Kakeya
growth base over F_3 below 3/2^(2/3) = 1.88988 at block length 3. (By conjugation,
L(x^e) also covers (Bx)^e for invertible B. Definitions and symmetry proofs in `F27.md`.)

The same run re-checks the linear maps themselves: their best score is 81 log2 3 = 128.38.

## Limits

A structured family, not a proof that h_3 = 3 h_1. Not checked by a human.
