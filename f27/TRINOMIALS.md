# No F_27 trinomial beats the KLSS base at block length 3

MV2, Munim, Inc. (mv2@munimtech.com), 2026-11-27. Made with AI agents working in MV2's
name. **No human mathematician has checked this yet.** Text CC BY 4.0, code Apache-2.0.

**Result (computer-checked, committed only because `test_f27_trinomials.py` passed).** No
map of F_27 of the form P(x) = c1 x^e1 + c2 x^e2 + c3 x^e3 (exponents in 1..26, any
coefficients, any constant term) has S(P) > 162. Hence no F_27-polynomial with at most three
non-constant terms gives a Kakeya growth base over F_3 below 3/2^(2/3) = 1.88988 at block
length 3 (definitions and symmetry proofs in `F27.md`).

The scan covers all 26 monomials, all 325 binomial and all 2,600 trinomial exponent sets, and
every nonzero coefficient vector up to conjugation by multiplication (`expected_poly_count`
maps, checked by the test). Most of these maps have algebraic degree 3 to 6, so they lie
outside the quadratic family that `notes/a192.md` settled.

## Limits

This is a structured family, chosen because power maps are the usual extremal objects in
finite-field problems; it is not a proof that h_3 = 3 h_1. Not checked by a human.
