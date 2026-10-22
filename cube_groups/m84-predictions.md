# Job m84: predictions, written 2026-10-22 ~01:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m84 (cube_groups/m84.py) splits two more classes of (B6) at t = 7 and dim V = 9 with d = 1
whose rank-0 sweep was open (job m64a: UNKNOWN at 150 s) by the second matrix A_(v_1)
(Proposition 33, notes/a52.md; counts by job m66), exactly as m81 split o009_c005 and o009_c006.
The rank-0 instances run too, each with the 21 negative unit clauses of Lemma 93 (b). Everything
but the lists is m69.py, imported unchanged.

- **m84a:** o009_c007 (|G| = 192, 3839 orbits: 255, 1792, 1792 of rank 0, 1, 2 on X_1): 3839
  instances, 255 with Lemma 93 (b).
- **m84b:** o010_c000 (|G| = 192, 3839: 255, 1792, 1792): the same counts.

m81 met its pace rule (median UNSAT wall 1.02 and 1.07 s; 11 and 16 open, each at most 30; no
SKIPPED instance, 80 and 87 minutes of solving), so m84 is queued under the plan m79-predictions.md
set out for the remaining open-sweep classes.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's class, unchanged (as in m81-predictions.md, item 1).
2. m84's own check: the class split here is not among the 30 classes closed by the split, nor among
   the four split before and re-run in m83, nor among m83's two tails.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses, from m81 (same |G| and orbit counts: 11 and 16 open; in m81b one of rank 1 and one of
rank 2, which m81-predictions.md did not expect):

- **Every instance of rank 1 and 2 UNSAT: about 60% per class.**
- **Some rank-0 instances open after this pass: about 90%;** about 5 to 30 (low confidence).
- **The class empty after this one pass: about 5%.**
- **Median UNSAT wall at most 3 s (high confidence).**
- **No SKIPPED instance: about 80%** (m81 took 80 and 87 minutes of the 150).
- **The open rank-0 roots repeat by m66 index across the pair-9 classes:** at least 5 of each
  class's open rank-0 instances sit at an m66 index also open in o009_c005 or o009_c006 (13824,
  16896, 17920, 32768, 49152, 50688, 181760, 182272, ...): about 60% for m84a (pair 9), no guess
  for m84b (pair 10).

Rules:

- **All split instances UNSAT:** the class is empty, (B6) goes up by one, the next corollary.
- **1 to 30 open (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL, then 5 of XOR
  (m83's pattern). **More than 30:** read them by rank and by place in m66's order before queueing
  more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
