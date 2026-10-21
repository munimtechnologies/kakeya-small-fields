# Job m45 (m45a, m45b): predictions, written 2026-10-20 ~03:10Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m45.py (Apache-2.0), which
runs m42.py unchanged (a copy of the m42.py that job m42a ran), with sat_aniso.py from the
repository. Setting: notes/a27.md (Lemma 83) and notes/a32.md (the results of job m42a).

## Why this job

Job m42a (2026-10-19 23:51 to 2026-10-20 01:44 UTC) held every graded check (96 of 96) and split
(B6) into 68 classes of A_u. Of the 34 classes in its half, 4 were UNSAT (143 to 189 s) and 30 were
UNKNOWN at their budget of 194 to 202 s. The decision rule of m42-predictions.md says: "UNKNOWN or
SKIPPED classes: one more job with at least 3 times the budget each". m45 is that job for these 30
classes. The other 34 classes of (B6) are job m42b's, which has not run yet.

    m45a   the 15 open classes in pair orbits 9, 10, 12; 156 minutes, at most 11 per class
    m45b   the 15 open classes in pair orbits 0, 2, 4, 5, 6, 7, 8, 11; same budget

Each class gets an equal share of what is left (the first gets about 10.4 minutes, at least 3 x 202
s = 606 s unless the check step is slow), at most 11 minutes.

## Graded (each must hold)

1. m45.py --part check: m42.py's classification of (B6), recomputed with the same code and seeds,
   has 68 classes with per-pair counts 1, 1, 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12 (as m42a); the 13
   pairs are the ones m42a recorded; each of the 30 names has the representative that m42a
   recorded, with kernel X_1 and image R of its pair; the probe instance has 79 hint conditions
   and consistent unit clauses; the batches split the 30 names 15 + 15.
2. Any SAT must be verified (a system, anisotropic, in the normal form), with rank A_u = 3 and
   every rank <= 4.

A failure of 1 means a bug or a transcription error: fix it, re-run as -v2, count nothing from
that job.

## Exploratory, with the decision rule

Guesses (low confidence; nothing at t = 7 and rank 3 has been timed beyond 200 s): no SAT. Batch a
(where all four UNSATs of m42a were, in pair orbit 12): 5 to 11 of 15 UNSAT. Batch b: 2 to 8 of 15
UNSAT. At t = 6 the analogous shape needed up to 74 minutes for its last classes (jobs m36, m37),
so many classes may stay open.

Rule:
- Every class of (B6) UNSAT, over m42a, m42b, m45 and any follow-up, with every graded check held:
  **no anisotropic system with t = 7 and dim V = 9 has an element of rank exactly 3 in (B6)**,
  computer-assisted.
- Classes still UNKNOWN after m45: do not escalate blindly. First write down (in a note) how long
  the solved classes took and whether one more pass at about 30 minutes per class fits the shared
  queue; otherwise split the class further by hand (a second fixed matrix, as Lemma 71 at t = 6).
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
