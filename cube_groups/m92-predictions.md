# Job m92: predictions, written 2026-10-22 in the run that started at 23:25Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m92 (cube_groups/m92.py) re-runs the 45 split instances that jobs m91a and m91b left open in
the last two classes of (B6), each class in its own group (m90.py's pattern, imported code
unchanged):

- **m92a:** the 25 of o003_c000 (d = 2), all of rank 0 on X_1 with Lemma 93 (b), each UNKNOWN at
  20 s in m91a.
- **m92b:** the 20 of o005_c000 (d = 2): 18 of rank 0 (UNKNOWN at 20 s) and 2 of rank 1, a0335 and
  a0463 (UNKNOWN at 10 s).

Each instance gets CaDiCaL for at most 300 s, then, if still open, CryptoMiniSat with native XOR for
300 s. What is known: every leftover re-run with these caps has closed so far (450 of 450, the
slowest under 245 s); the 20 of o010_c001 closed in 1.33 to 84.49 s (median 51.79 s) and the 49 of
m89 in 11 to 95 s. In o003_c000's sister class o003_c001, all 32 rank-0 leftovers closed in m89.

Sizing: at about 60 s per rank-0 re-run, about 25 minutes for m92a and 20 for m92b; at the full
cap in both arms, 250 and 200 minutes, past the 150-minute group budget (instances not reached
would be SKIPPED, which counts as open).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's 14 checks with the planted control at t = 6, in both arms.
2. The group's class against m66's run (structure, |G|, |Adm|, orbit counts by rank on X_1), every
   root recomputed and admissible, of its rank, distinct with its sum with A_u.
3. The list: both groups together are exactly the 45 open instances of m91a and m91b, once each,
   by class (25 and 20) and by rank (25 / 0 / 0 and 18 / 2 / 0); each row's name, m66 index, orbit
   size, A_(v_1) and rank equal to the recomputed root; Lemma 93 (b) on exactly the rank-0 ones;
   neither class among the 45 closed before.
4. The plan: CaDiCaL then XOR at the full cap for each; hints 79, units 49 + 21 on the first rank-0
   instance in both arms (49 on the first rank-1 one in m92b); the Lemma 93 instance equal to the
   plain one plus exactly 21 negative unit clauses, in both arms.
5. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

- **No SAT anywhere: about 98%.**
- **All 25 of m92a UNSAT within 300 s of CaDiCaL: about 85%. All 20 of m92b: about 85%. Both,
  so (B6) is empty: about 75%.**
- **Slowest UNSAT wall at most 150 s over both groups: about 70%.**
- **Median UNSAT wall (CaDiCaL) between 20 and 100 s in each group: about 70%.**
- **a0335 and a0463 (rank 1) each close in at most 60 s: about 80%.**
- **Each group's solve part at most 60 minutes: about 80%. No SKIPPED: about 95% per group.**
- **No instance needs the XOR arm: about 85% per group.**

Rules:

- **A group with all its re-runs UNSAT:** its class is empty (Corollary 117 for o003_c000, 118 for
  o005_c000 if both close; numbered in the order the notes report them).
- **Both classes empty:** (B6) is empty, all 68 classes. With Proposition 35 ((B5) empty) and the
  reductions listed in notes/a68.md, that is A(7) <= 8 (computer-assisted, Theorem 33), which
  settles the pair (13, 8). Write it with every dependency listed (hand lemmas, Proposition 33,
  Lemma 93, every job and its counts) before any post; then certify the hardest instances with
  DRAT, beginning with these 45.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split by hand before
  queueing anything for it.
- **The host interrupts a group:** read the per-instance records, report them as such, and file the
  unreached part only, under a new name.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
