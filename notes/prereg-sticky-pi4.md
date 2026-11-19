# Pre-registration: sticky-pi4-v1 (a proved lower bound for pi_4)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19, written before any run. Made with AI agents
working in MV2's name. Code: `sticky_pi4.py` (needs `sticky_pi3.py`), tests `test_sticky_pi4.py`.
Theory: notes a188 (Lemma 162) and a189 (Proposition 84, Lemma 163).

## Question

pi_k is the least slice product |S_0||S_1||S_2| of a full sticky tree of height k over F_3.
Question S7 (sticky Kakeya base below 2) holds iff pi_k < 8^k for some k (a188, Cor. 78.1).
a189 proved pi_3 = 512. Is pi_4 = 4096?

## Method (fixed now)

Exact height-2 vectors (all 27^4 trees), then unions relaxed to maxima at heights 3 and 4.
M3 = the coordinatewise-minimal vectors of { node_lower(root, kids) : kids in M2^3, all 27 roots }.
Height 4, quadratic roots: exact minimum over all ordered (A, B, C) in M3^3 of
(A0 + max(B0, C0)) (B1 + max(A1, C1)) (C2 + max(A2, B2)), with a pruning that only skips triples
whose product provably is at least the current best. Affine roots: the bound 9 · min over M3 of
the product (Lemma 162). The reported lower bound LB4 is the smaller of the two.

## Rules

- **Sanity / BUG.** Tests must pass. In the run: the height-3 quadratic minimum must be 512
  (as in sticky-beam-v1), the least height-2 product 64, every M3 product >= 512, the height-4
  quadratic minimum <= 4096 (the classical tree), and LB4 >= 3456 = (27/4) · 512. Any failure is
  a BUG and nothing is concluded.
- **PI4-EXACT.** LB4 = 4096. Then pi_4 = 4096 (the classical tree attains it), and any
  certificate for S7 has height at least 5.
- **PI4-OPEN.** LB4 < 4096. Then pi_4 lies in [LB4, 4096] and the relaxation is too weak at
  height 4. The minimiser's child shapes (from M3) are recorded; a follow-up search tries to
  realise them with real trees. Nothing about S7 is concluded.

## Prediction (made before the run)

PI4-EXACT, with low confidence (about 60%). Reason: at height 3 the relaxation was tight (512),
and the max-game of a185 only beats 2 with lopsided shapes built over several levels. If the
prediction fails, the witness is the more useful outcome, because it says where to look.
