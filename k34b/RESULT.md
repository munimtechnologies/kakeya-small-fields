# k34b: a second, independently written computer route to K(3, 4) = 28

Made with AI agents working in MV2's name (MV2 of Munim, Inc., mv2@munimtech.com).
**Not checked by a human mathematician.** Text CC BY 4.0, code Apache-2.0.

This file is committed only together with `results/indep-q4-T28.json` and only if
`test_k34b_complete.py` passes on it, that is, only if the independent search finished every
subproblem and found no Kakeya set of F_4^3 with 27 or fewer points.

## What it confirms

`k34/` (RESULT.md, PROOF.md) showed by an exhaustive slice search that every Kakeya set in F_4^3
has at least 28 points, so the 28-point even-q construction of Kopparty, Saraf and Sudan is optimal
and K(3, 4) = 28. `k34b/indep.py` repeats the search with code written from scratch, sharing
nothing with `k34/slices.py` or `k34/verify.py`:

* F_4 from a logarithm table; the plane's symmetry group (AGL(2, 4) x Frobenius, order 5760)
  built by listing every invertible matrix, translation and field automorphism, not from
  generators; orbit representatives found by applying the whole group;
* its own depth-first search over maps f from the 16 transversal directions onto S_0, with the
  same hand bound |K| >= r + sum_{c != 0} max(|S_c| + ceil(N_c / r), r) (PROOF.md, step 4) and the
  shear normalisation f(0) = S_0[0];
* its own exact placement of the five horizontal directions (a subset dynamic program over the
  four parallel planes);
* its own Kakeya checker.

## Result

For all 21 orbit representatives S_0 with |S_0| <= 6, the search finished and found no Kakeya set
below 28 points (`results/indep-q4-T28.json`: `"complete": true`, `"sets_below_T": 0`; the
smallest exact leaf value is 28, reached on many branches, i.e. there are many 28-point sets).

## Controls (`results/controls-b.json`, test_k34b_run1.py)

* group orders 432 (F_3) and 5760 (F_4); orbit sizes add up to the binomial coefficients;
  orbit counts 1, 1, 2, 4, 5, 8 for r = 1..6;
* the same code over F_3 finds no Kakeya set below 13 and finds a 13-point one, reproducing
  K(3, 3) = 13;
* asked for sets below 29 on the orbit of the 2 x 2 grid, it reaches a 28-point set in F_4^3,
  which its checker accepts.

## Limits

Both routes rest on the same short hand reduction (PROOF.md), which no human mathematician has
checked; the two programs check each other's code, not the reduction.
