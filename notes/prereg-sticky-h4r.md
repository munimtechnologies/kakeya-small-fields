# Pre-registration: sticky-h4r-v1 (exact height 3, relaxed above: a bound for pi_5 against 8^5)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-20, written before the job runs.
Made with AI agents working in MV2's name. **No human mathematician has checked this note.**
Text CC BY 4.0; code `sticky_h4r.py` (uses `sticky_h3.py`) and tests `test_sticky_h4r.py`, Apache-2.0.
Context: a188 (Theorem 78, Corollary 78.1: S7 holds iff some full sticky tree has slice product
< 8^k), a190 (the game: pi_5 >= 27,000), a194 (Proposition 88: pi_4 = 4096).

## Question

Is pi_5 = 8^5 = 32,768? If yes, any certificate for S7 (sticky Kakeya growth base over F_3 below 2)
has height at least 6. If not decided, how far above the game value 27,000 does an exact
height-3 layer push the proved lower bound?

## Method (fixed in advance)

1. As in `sticky_h3.py`: enumerate all 27^4 height-2 trees, then compute the exact quadratic
   height-3 vectors (|A0| + |B0 u C0|, |B1| + |A1 u C1|, |C2| + |A2 u B2|), now over the **whole**
   range (no restriction to the down-set W). Affine roots at height 3 stay relaxed. E3 = the
   minimal elements. Every real height-3 vector dominates an element of E3.
2. F4 = the union >= max front one level above E3 (all 27 root maps, in closed form:
   `next_front`), F5 = one more level (optional, only if predicted to fit in the time limit).
3. pi_5 >= min(least quadratic-root product over F4, 9 * pi_4 = 36,864) (Lemma 162 with
   Proposition 88). Optional: pi_6 >= min(least quadratic-root product over F5, 9 * that bound).

## Self-checks (any failure = BUG, no claim)

Height 2: 531,441 trees, 96 vectors, 19 minimal. `next_front` of the 19 minimal vectors equals the
node-by-node game front at height 3 (112 vectors, least product 512). Game front at height 4: 649
vectors, least product 3,971; game quadratic minimum at height 5: 27,000 (all three from
sticky-front-v1, a190). E3: least product 512 (Proposition 84), every vector above the game
front, symmetric under the six slice permutations, (8,8,8) dominated, and E3 restricted to W is
exactly {(4,12,12), (12,4,12), (12,12,4)} (sticky-h3-v1). F4: least product exactly 4,096
(Proposition 88).

## Reading rules

- **PI5-EXACT**: bound >= 32,768. Then pi_5 = 32,768 and no S7 certificate has height <= 5.
- **PI5-OPEN**: bound L < 32,768. Then pi_5 lies in [L, 32,768]; L > 27,000 is a new proved
  bound. The job names the F4 children of the cheapest height-5 node and how each comes from E3
  (with real height-3 trees). Next step: an exact height-4 check on those shapes (a real height-5
  tree with product < 32,768 would settle S7 in the positive: sticky base below 2).
- **INCOMPLETE**: the exact search hit its time limit. No claim.
- The optional height-6 numbers are reported as a proved lower bound for pi_6 only; they decide
  nothing by themselves, since by a185 (Theorem 73) every pure relaxation eventually falls below
  8^k at some height.

## Predictions

- PI5-OPEN, about 60% confidence (the relaxation re-enters at height 4, where the game already
  found shapes below the classical ones).
- If PI5-OPEN: the bound is strictly above 27,000, about 85% confidence.
- |E3| is between 60 and 400, about 70% confidence.
