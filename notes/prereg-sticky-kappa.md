# Pre-registration: sticky-kappa-v1 (single-tree search for question S7)

MV2 of Munim, Inc. (mv2@munimtech.com), written 2026-11-20 before the job ran.
Made with AI agents working in MV2's name. No human mathematician has checked it.
Code: `sticky_kappa.py` (tests `test_sticky_kappa.py`). Theory: `notes/a195.md`.

## Question

Is there a full sticky tree A of height h in {3, 4, 5, 6} over F_3 with
kappa(A) = min_{i,w} |A_i| + |A_{i+1} u (A_{i+2} + w)| < 2^(h+1)?
By Proposition 89 such a tree gives a tree of height h+1 with slice product below 8^(h+1), which
answers S7 positively (sticky Kakeya sets over F_3 grow with base below 2).

## Method (fixed before the run)

1. Self-checks: kappa_1 = 4 and kappa_2 = 8 over all 27 and 531,441 trees; Proposition 89 on 600
   random trees (build A', count its slices directly); the incremental engine against a direct
   slice computation after random moves; the classical tree gives 2^(h+1) at h = 1..6.
2. Simulated annealing on kappa at heights 3, 4, 5, 6 (time shares 4%, 24%, 32%, 40% of a
   8,400 s budget; 20k, 60k, 80k, 80k steps per restart; restarts cycle through classical,
   classical with 8% noise, uniform random, random node-affine starts). Moves: change one value
   of P (75%); copy a subtree onto another node of the same depth with a random translation and
   slice relabelling rho_c (25%). Temperature 0.05 -> 0.002 in units of 2^(h+1). Seed 20261120.
3. Every tree with kappa < 2^(h+1) is rebuilt: kappa by brute force over i and w, A' built, its
   slices counted from the definition, product compared with 8^(h+1).

## Verdicts

- **BUG**: any self-check fails. Fix and re-run as -v2; no claim.
- **CONFLICT**: a verified tree has kappa_3 < 16 (contradicts Proposition 88) or kappa_4 < 30
  (contradicts a190's pi_5 >= 27,000). Re-examine both computations before any claim.
- **S7-TRUE**: a verified tree with kappa < 2^(h+1). This proves that sticky Kakeya sets over F_3
  grow with base at most kappa^(1/(h+1)) < 2 (a188 Corollary 78.1). Write it up with the explicit
  tree.
- **NOT-FOUND**: no such tree. This is weak evidence for Conjecture T only, and no claim about
  pi_5 is made from it.

## Predictions

- NOT-FOUND: 85%.
- The best kappa found equals 2^(h+1) at every height 3-6 (the classical start guarantees at most
  2^(h+1)): 85%.
- At least one non-classical tight tree (kappa = 2^(h+1), slice sizes not all equal) is found at
  h = 4: 70%.
- All self-checks pass: 85%.
