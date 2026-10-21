# Job m79: predictions, written 2026-10-21 ~20:30Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m79 (cube_groups/m79.py) splits three classes of (B6) at t = 7 and dim V = 9 with d = 1 whose
rank-0 sweep was open (job m64a: UNKNOWN at 150 s) by the second matrix A_(v_1) (Proposition 33,
notes/a52.md; counts by job m66). Because the sweeps were not UNSAT, Lemma 93 (a) does not drop the
rank-0 instances: they run too, each with the 21 negative unit clauses of Lemma 93 (b), as m71a ran
them for o008_c002 and o010_c002. Everything but the lists is m69.py, imported unchanged.

- **m79a:** o008_c000 (|G| = 384, 2023 orbits: 135, 944, 944 of rank 0, 1, 2 on X_1) and
  o008_c001 (|G| = 576, 1287: 87, 600, 600): 3310 instances, 222 with Lemma 93 (b).
- **m79b:** o008_c003 (|G| = 384, 1975: 135, 920, 920): 1975 instances, 135 with Lemma 93 (b).
- **Written while four jobs were pending** (m75b, m78a, m78b, m78r), so it is staged, not queued.
  A later run queues it once fewer than four are pending. If it is queued with more pending, the
  departure is written here first.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's classes, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses on A_(v_2), ..., A_(v_(kd-1)) at X_1's columns, in both arms.
2. m79's own check: no class split here is among the 27 classes closed by the split.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses, from m71a (o008_c002 and o010_c002, the same d = 1 with an open sweep: every instance of
rank 1 and 2 UNSAT; 13 and 6 of the 69 rank-0 instances open at 10 s; all of them UNSAT at 300 s,
the slowest in 56.4 s):

- **Every instance of rank 1 and 2 UNSAT in all three classes: medium-high confidence.**
- **Some rank-0 instances open after this pass in each class: about 80%.** About 5 to 35 per class
  (low confidence), and every open instance of rank 0 (medium confidence).
- **A class empty after this one pass: about 15% each.**
- **Median UNSAT wall at most 3 s in each class (high confidence).** m76a-v2 and m77: 1.02 to 1.12 s.
- **No SKIPPED instance: about 75% for m79a, 90% for m79b.** At 1.1 s per instance with overhead,
  m79a's 3088 instances of rank 1 and 2 take about 57 minutes; its 222 rank-0 instances could take
  up to 20 s each (74 minutes) if many run to their budgets.

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary (Corollary 96 on, after any that m75b and m78 earn first).
- **1 to 30 open in a class:** re-run each with 5 minutes of CaDiCaL, then 5 of XOR, in the next
  job (m73's pattern). **More than 30:** read them by rank first, and look at where the open ones sit
  in m66's order before queueing more.
- **Pace:** median at most 3 s and at most 30 open per class: the remaining 17 classes of (B6)
  with an open sweep get the same treatment, about 2000 to 3300 instances per group. Above 8 s
  anywhere: re-estimate and look for a hand reduction first.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
