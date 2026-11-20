# Pre-registration: sticky-l4-v1 (can a height-6 cyclic triangle beat 31^(1/5)?)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-20, written before the job runs.
Made with AI agents working in MV2's name. **No human mathematician has checked this note.**
Text CC BY 4.0; code `sticky_l4.py` and tests `test_sticky_l4.py`, Apache-2.0 (they import
`sticky_s7.py`, `sticky_kexact.py`, `sticky_h3.py`, `sticky_h4r.py` from this repository).
Context: a196 (Theorem 79), a197 (Lemmas 166-167), a198 (Theorem 81: pi_5 = 29,791, kappa_4 = 31,
60 <= kappa_5 <= 62).

## Question

The sticky Kakeya base over F_3 is at most kappa_h^(1/(h+1)) for every h, and at most 31^(1/5) = 1.98734
from height 5 (a196). By a198 no other height-5 tree does better. At height 6 a cyclic triangle of a
height-5 tree would beat 1.98734 if and only if **kappa_5 <= 61**. Known: 60 <= kappa_5 <= lambda_4 <= 62.
Does kappa_5 (or the pair value lambda_4) drop to 61 or below?

## Method (fixed in advance)

1. Recompute, as in sticky-h4r-v1, the proved fronts M2 (height 2, 19 vectors), E3 (height 3, 112)
   and F4 (height 4, 670, least product 4,096). Every real slice vector of a tree of that height
   dominates an element of the front (a198).
2. CP-SAT (OR-Tools 9.x, 4 workers), one Boolean per value-table entry and per point, with each tree's
   slice sets as supersets of its true slices and the cut "the padded slice-size vector dominates some
   front vector" (valid: real configurations satisfy it with the true sets; the optimum is unchanged).
   - `pair_cut(h, F)`: min lambda(A, B) over pairs of height-h trees, both cut by F.
   - `kappa_cut(h, F)`: min |S_0| + |S_1 u S_2| over all height-h trees, written as a free root map
     plus three children of height h-1 cut by F (S_t = union over x of {g(x) + t x} x S_t(child x)),
     plus per-plane cardinality cuts. No assumption on the root map (no use of Proposition 92).
3. Runs in order: kappa3 (M2 cut, 10 min), lambda2 (M2, 10 min), lambda3 (E3, hint a196 pair, 20 min),
   kappa4 (E3, hint tree H, 30 min), **lambda4 (F4, value capped at 61, 120 min)**,
   **kappa5 (F4, value capped at 61, 140 min)**.
4. Every solution found is rebuilt in pure Python: its cyclic triangle (and for pairs the tree N) is
   built as an explicit map, checked to be sticky, and its slices counted by brute force; the children's
   slice vectors are checked against the front. Only rebuilt values count.

## Verdicts

- **BUG**: front counts differ from sticky-h4r-v1; kappa3 or lambda2 not OPTIMAL 16; a rebuilt
  solution fails its checks; an OPTIMAL objective differs from its rebuilt value; a bound exceeds a
  rebuilt value; lambda3 or kappa4 below 31 or with a bound above 31; a height-5 value below 60; kappa5
  INFEASIBLE while lambda4 has a rebuilt value <= 61. Then nothing public about the values; fix, -v2.
- **H6-BEATS**: a rebuilt lambda4 or kappa5 value v <= 61. Then beta_s <= v^(1/6) (61^(1/6) = 1.98407,
  60^(1/6) = 1.97872), a new upper bound. Before anything public: re-verify the witness in a separate
  small script under test_first, then a theorem note and article.
- **KAPPA5-62**: kappa5 INFEASIBLE at <= 61. Then kappa_5 = lambda_4 = 62 (computer-assisted, CP-SAT):
  no cyclic triangle of height 6 beats the a196 base; a better base would need height >= 7 or another
  operation.
- **LAMBDA4-62**: lambda4 INFEASIBLE at <= 61 but kappa5 undecided. Then lambda_4 = 62: the pair
  construction of a196 does not improve at the next height.
- **UNDECIDED**: none of the above; the solver bounds are reported as computer-reported only.
- Flags LAMBDA3-EXACT-31 and KAPPA4-EXACT-31 (OPTIMAL 31) are independent CP-SAT confirmations of
  Theorem 81's consequence kappa_4 = lambda_3 = 31; KAPPA4-EXACT-31 needs no Proposition 92.

CP-SAT optimality and infeasibility claims are not independently checkable certificates; any value
decided here will be stated as "computer-assisted (CP-SAT)".

## Predictions (written before the run)

- Fronts and sanity runs pass: 85%.
- lambda3 OPTIMAL 31 within 20 min: 75%. kappa4 OPTIMAL 31 within 30 min: 45%.
- lambda4 decided (INFEASIBLE or a value <= 61): 35%. kappa5 decided: 15%.
- H6-BEATS: 10%. KAPPA5-62: 12%. LAMBDA4-62 (only): 25%. UNDECIDED: 43%. BUG: 10%.
  (Annealing over height-4 pairs, sticky-pair-v1, never got below 69 on its own; the best known pair
  is the product construction (H, H(-d)) with 62, which is weak evidence that 62 is the true value.)
