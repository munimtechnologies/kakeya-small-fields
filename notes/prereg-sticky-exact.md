# Pre-registration: sticky-exact-v1 (exact minimum sticky Kakeya sets in F_3^4 and F_3^5)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19, written before any run. Made with AI agents
working in MV2's name. Code: `sticky_exact.py` (tests `test_sticky_exact.py`), built on
`sticky_planes.py` (note a186).

## Question

U*(n) is the least size of a sticky Kakeya set in F_3^n. Note a186 proves U*(n) = 2^(n+1) - 1
for n <= 3 and 29 <= U*(4) <= 31. Question S5 asks whether the classical set
{0,1}^n ∪ {0,2}^n (2^(n+1) - 1 points) is always the smallest sticky Kakeya set. The game
relaxation cannot answer it: its growth constant is below 2 (a185, Theorem 73).

## Method

CP-SAT over all sticky families (model "full": one map per prefix, the translation symmetry
fixed per depth) and over the reduced form of Theorem 74 (model "reduced": root map (0,0,0),
subtree 2 the relabelled copy of subtree 1). Both have optimum U*(n). Every solution is
re-checked in pure Python: its Kakeya set is recomputed from the maps, its size compared with
the solver's objective, and every direction's line checked. We also compute the game bound G(5)
of Corollary 74.1, using U*(4) >= 29, and again with the best proved bound on U*(4) if it is
higher.

Plan: n = 2 and 3 in both models (sanity), n = 4 reduced (4,500 s), n = 4 full (3,000 s),
n = 5 reduced (3,600 s), 4 workers.

## Rules (fixed now)

- **Sanity.** Both models must return OPTIMAL 7 for n = 2 and OPTIMAL 15 for n = 3, with matching
  verified sizes. Otherwise the run is a BUG and nothing below is used.
- **n = 4.**
  - Any verified sticky set with fewer than 29 points, or a solver bound above a verified size,
    means BUG: a186 proves U*(4) >= 29.
  - A verified sticky set with 29 or 30 points means **S4-BREAK**. Stickiness does not force
    the classical size, and the set is published with its maps.
  - A proved bound of 31 from either model means **S4-CLASSICAL**: U*(4) = 31 = 2^5 - 1.
  - Anything else is UNDECIDED, and the bounds are reported.
- **n = 5.** A verified sticky set with at most 62 points is **S5-BREAK**. A proved bound of 57
  or more is **S5-SEPARATION**: no Kakeya set of 56 points in F_3^5 (one exists,
  kakeya-conjecture v1.1.0) is sticky. Otherwise we report the bounds.
- **G(5).** If G(5) >= 57, S5-SEPARATION is also proved by the game bound alone, independently
  of the solver.

## What each outcome would mean

S4-CLASSICAL extends "the classical set is the smallest sticky set" to n = 4. That would be
evidence for S5, though not a proof. S4-BREAK would be the first sticky Kakeya set over F_3
smaller than the classical product. That is the direction suggested by a185's Theorem 73, and
it would make the realisability of cheap game trees the central question.
