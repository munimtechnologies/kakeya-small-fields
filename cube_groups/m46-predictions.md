# Job m46 (m46a, m46b): predictions, written 2026-10-20 ~04:10Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m46.py (Apache-2.0), which
runs m42.py unchanged (the m42.py that jobs m42a and m42c ran), with sat_aniso.py from the
repository. Setting: notes/a27.md (Lemma 83) and notes/a33.md (the results of job m42c).

## Why this job

Job m42c (2026-10-20 02:13 to 03:46 UTC) solved the first half of (B5): of its 210 classes of A_u,
168 were UNSAT and 42 UNKNOWN. The undecided classes had budgets of about 40 to 63 s (two of them
107 and 475 s). The decision rule of m42-predictions.md says: "UNKNOWN or SKIPPED classes: one more
job with at least 3 times the budget each". m46 is that job for these 42 classes. The other 210
classes of (B5) are job m42d's, which has not run yet; its leftovers get their own follow-up.

    m46a   the 20 open classes with X_1 inside H0 (pair orbits 0 to 19); 156 minutes, at most 10 per class
    m46b   the 22 open classes with X_1 outside H0 (pair orbits 20 to 48); same budget

Each class gets an equal share of what is left (about 7.8 and 7.1 minutes, at least 3 x 63 s = 189 s
unless the check step is slow), at most 10 minutes.

## Not queued yet

m46 is designed and staged (compete-staged/m46a, m46b) but was not queued in the run that wrote it:
the shared 2-slot queue already held 12 of this field's jobs (m42b, m42d, m43a-d, m44a-d, m45a,
m45b), and the rule of the field's playbook is not to add more until those report. It is queued once
m42d reports (so that its leftovers can be added as a batch c) or once the queue has room.

## Graded (each must hold)

1. m46.py --part check: m42.py's classification of (B5), recomputed with the same code and seeds,
   has 420 classes with the per-pair counts of M42C_PER_PAIR (as m42c: 3, 1, 2, 13, 3, 9, 3, 10, 5,
   10, 9, 10, 3, 6, 26, 14, 26, 14, 12, 27 for X_1 inside H0, 206 in all, then 1, 5, 2, 4, 2, 10, 5,
   10, 9, 6, 12, 1, 1, 1, 5, 4, 5, 4, 10, 23, 4, 2, 3, 14, 9, 14, 9, 12, 27, 214 in all); the 49
   pairs are the ones m42c recorded (X_1 = span(e_0, e_1, e_2, e_3) for pairs 0 to 19 and
   span(e_0, e_1, e_2, e_6) for 20 to 48, R as in PAIR_R); each of the 42 names has the
   representative that m42c recorded, with kernel X_1 and image R of its pair; the probe instance has
   111 hint conditions and consistent unit clauses; the batches split the 42 names 20 + 22.
2. Any SAT must be verified (a system, anisotropic, in the normal form), with rank A_u = 3 and
   every rank <= 4.

A failure of 1 means a bug or a transcription error: fix it, re-run as -v2, count nothing from
that job.

## Exploratory, with the decision rule

Guesses (low confidence): no SAT. In m42c, 80 of the 168 UNSAT answers came in under 10 s, 86 in
10 to 60 s and 2 in about 4 minutes, and the budget here is 7 to 8 minutes, so: batch a 8 to 16 of
20 UNSAT, batch b 9 to 18 of 22. The five classes with d = dim(X_1 n R) = 3 (pairs 0, 2, 20, 32;
A_u^2 = 0) are the most likely to stay open, as every tried class with d = 3 did in m42a and m42c.

Rule:
- Every class of (B5) UNSAT, over m42c, m42d, m46 and any follow-up, with every graded check held:
  **no anisotropic system with t = 7 and dim V = 9 has an element of rank exactly 3 in (B5)**,
  computer-assisted.
- Classes still UNKNOWN after m46: do not escalate blindly. First write down how long the solved
  classes took and whether one more pass at about 30 minutes per class fits the shared queue;
  otherwise split the class further by hand (a second fixed matrix, as Lemma 71 at t = 6), or find
  the hand fact that a33.md asks for (the kind-L and d = 3 patterns).
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
