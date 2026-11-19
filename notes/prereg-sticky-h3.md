# Pre-registration: sticky-h3-v1 (exact unions at height 3; is pi_4 = 4096?)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19, written before the job runs.
Made with AI agents working in MV2's name. **No human mathematician has checked this note.**
Text CC BY 4.0; code `sticky_h3.py` and tests `test_sticky_h3.py`, Apache-2.0.
Context: a188 (Theorem 78: S7 holds iff some full sticky tree has slice product < 8^k), a189
(pi_3 = 512), a190 (pi_4 >= 3971 from the game; Lemma 164: the game is not exact at height 3).

## Question

Is pi_4 = 4096, i.e. does every full sticky tree of height 4 over F_3 have
|S_0||S_1||S_2| >= 8^4? If yes, any certificate for S7 (sticky Kakeya base over F_3 below 2) has
height at least 5.

## Method (fixed in advance)

1. Enumerate all 27^4 height-2 trees; record their slices as subsets of F_3^2.
2. Compute W, the set of height-3 vectors that could take part in a height-4 quadratic node of
   product < 4096 when the other two children range over the game front at height 3 (a superset
   of all real possibilities, because real vectors dominate the game front). W is a down-set.
3. For quadratic roots at height 3, compute the exact vectors
   (|A0| + |B0 u C0|, |B1| + |A1 u C1|, |C2| + |A2 u B2|) over all real children, restricted to W.
   Exact reductions only: children whose slice sets are supersets of another child's with no
   smaller size are dropped; one child is taken up to the 108 lower-triangular affine maps of
   F_3^2, applied to all three children at once (this preserves every union size).
   Affine roots at height 3 are kept relaxed (union >= max), which is still a lower bound.
4. H3 = minimal elements of the result. Relax height 4 (union >= max) over H3; affine roots at
   height 4 cost at least 9 · 512 = 4608 (Lemma 162 with Proposition 84).

## Reading rules

- **PI4-EXACT**: least height-4 product >= 4096. Then pi_4 = 4096 (the classical tree attains
  it), and no certificate for S7 has height <= 4. A computer-assisted proposition.
- **PI4-OPEN**: least product L < 4096. Then pi_4 lies in [max(L, 3971), 4096], and the job names
  real height-3 trees (witnesses) for the minimising children. Next step: an exact check of
  unions at height 4 for those shapes (a real tree with product < 4096 would settle S7: base < 2).
- **INCOMPLETE**: the time limit (30,000 s) ended the exact search. No claim is made.
- **BUG**: any self-check fails (a sampled group image of a tree is not a tree; height-2 counts
  differ from 96 vectors and 19 minimal; the game front at height 3 differs from 112 vectors with
  least product 512; an H3 vector lies below the game front; H3 is not symmetric under the six
  permutations of slices; the classical (8,8,8) is in W but not dominated; an H3 product < 512).
  No claim is made.
- Also reported: the game-front vectors in W that no real height-3 vector attains (those the
  exact unions raise). Prediction: (7,7,12) is among them (Lemma 164 rules out its game
  derivation; other derivations might exist).

## Prediction

PI4-EXACT, with about 55% confidence. The least product in the game, 3971, needs three exact
coincidences of slice sets at height 4 on top of shapes that, by Lemma 164, are already not built
the game's way at height 3.
