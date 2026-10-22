# Job m91: predictions, written 2026-10-22 in the run that started at 21:28Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m91 (cube_groups/m91.py) splits the last two open classes of (B6), one per group, by m69.py's
second-matrix split imported unchanged (as m88.py split o005_c003):

- **m91a:** o003_c000 (d = 2, |G| = 1536, 1599 orbit roots: 255 of rank 0 on X_1 with Lemma 93 (b),
  896 of rank 1, 448 of rank 2).
- **m91b:** o005_c000 (d = 2, |G| = 512, 1913: 135, 920, 858).

Each instance gets CaDiCaL for a share of what is left of 150 minutes, at least 10 s and at most
20 s, the most rank on X_1 first; instances not reached are SKIPPED (open).

What is already known (job m87a-b6rerun-v3, interrupted by the host after 68 minutes of its solve
part, so never graded; notes/a78.md): in o003_c000 all 1344 instances of rank 1 and 2 were UNSAT
(slowest wall 5.88 s, a0525), and of the first 24 of rank 0, at 10 s each, 13 were UNSAT and 11
UNKNOWN (a0042, a0124, a0206, a0288, a0327, a0352, a0511, a0524, a0537, a0576, a0615). In the
sister class o003_c001 (same |G| and counts), job m87b left 32 of rank 0 open at 10 s; 8 of the 11
are at the same positions k (a0042, a0288, a0352, a0511, a0524, a0537, a0576, a0615) and 2 within
4 of one (a0124 and a0128, a0206 and a0210); o005_c001
(sister of o005_c000) left 17 open at 20 s (16 of rank 0, 1 of rank 1). m91a repeats the 1344
already seen, so that the whole class is in one graded run.

Sizing: about 2.2 s per instance in all (m87a-v3: 1344 instances in about 49 minutes), so about 49
minutes of rank 1 and 2 in m91a and 65 in m91b; then each rank-0 instance gets the full 20 s, at
most 85 and 45 minutes. Both groups fit 150 minutes if the host is not much slower.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units 49
   on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly 21
   negative unit clauses, in both arms.
2. m91's own: the class is not among the 45 closed before.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

- **No SAT anywhere: about 98%.**
- **m91a: all 1344 of rank 1 and 2 UNSAT again: about 97%.** (They were all UNSAT in m87a-v3 at
  10 s; here the budget is the same or larger.)
- **m91a: 10 to 40 rank-0 instances open: about 65%; fewer than 10: about 20%; more than 40: about
  15%.** At least 8 of the 11 left open by m87a-v3 at 10 s still open at 20 s: about 60%.
- **m91b: 5 to 30 open: about 70%; at least one of rank 1 or 2 open: about 40%.**
- **Either class empty after this one pass: about 5% each.**
- **Median UNSAT wall at most 2 s in each class: about 85%.**
- **No SKIPPED instance: about 80% per group.**
- No guess on which positions stay open beyond the line above; overlaps with o003_c001 and
  o005_c001 are reported, not predicted.

Rules:

- **A class with all its instances UNSAT:** it is empty, (B6) goes up by one, the next corollary.
- **1 to 30 open in a class (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL,
  then 5 of XOR, in the next job (m90.py's pattern). **More than 30:** read them by rank and by
  place in m66's order; if they are all of rank 0 and not SKIPPED, re-run them in jobs of at most
  30 (as m89 did for o003_c001's 32).
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split by hand before
  queueing anything for it.
- **The host interrupts a group again:** read the per-instance records, report them as such, and
  file the unreached part only; do not re-file the same name.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
