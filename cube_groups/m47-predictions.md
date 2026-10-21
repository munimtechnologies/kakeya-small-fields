# Job m47 (m47a, m47b, m47c): predictions, written 2026-10-20 ~05:10Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m47.py (Apache-2.0), which
runs m42.py unchanged (the m42.py that jobs m42a and m42b ran), with sat_aniso.py from the
repository. Setting: notes/a27.md (Lemma 83), notes/a32.md (job m42a) and notes/a34.md (job m42b).

## Why this job

Job m42b (2026-10-20 01:44 to 04:07 UTC) solved the second half of (B6): of its 34 classes of A_u, 5
were UNSAT (161 to 243 s) and 29 UNKNOWN at budgets of 247 to 277 s. The decision rule of
m42-predictions.md says: "UNKNOWN or SKIPPED classes: one more job with at least 3 times the budget
each". m47 is that job for these 29 classes, as m45 is for the 30 that m42a left open.

    m47a   pair orbits 1, 3, 5, 8 (9 classes; d >= 2 except pair 8);  156 minutes, at most 15 per class
    m47b   pair orbits 7, 11, 12 (11 classes; where m42b's UNSAT answers were); 158 minutes, same cap
    m47c   pair orbits 9, 10 (9 classes); 156 minutes, same cap

Each class gets an equal share of what is left: about 15 minutes in a and c (the cap) and about 14.3
minutes in b, in every case at least 3 x 277 s = 831 s unless the check step is slow.

## Not queued yet

m47 is designed and staged (compete-staged/m47a, m47b, m47c) but was not queued in the run that
wrote it: the shared 2-slot queue held 8 of this field's jobs (m42d, m43d, m44a to m44d, m45a,
m45b). By the rule written in notes/a32.md before job m45 ran, m45's result decides: if it closes
most of its 30 classes at 10.4 minutes each, m47 is queued as designed; if it closes few, a pass at
15 minutes is unlikely to pay for 3 x 2.6 CPU hours, and the open classes of (B6) go to a hand
split instead.

## Graded (each must hold)

1. m47.py --part check: m42.py's classification of (B6), recomputed with the same code and seeds,
   has 68 classes with per-pair counts 1, 1, 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12 (as m42a and m42b);
   the 13 pairs are the ones they recorded; each of the 29 open names and the 5 UNSAT names of m42b
   has the representative that m42b recorded, with kernel X_1 and image R of its pair; those 34
   names are exactly m42b's half (per pair 0, 1, 0, 5, 0, 2, 0, 8, 1, 5, 4, 5, 3), which with m42a's
   half (1, 0, 1, 0, 2, 2, 2, 2, 4, 5, 5, 1, 9) gives the 68; the probe instance has 79 hint
   conditions and consistent unit clauses; the batches split the 29 names 9 + 11 + 9.
2. Any SAT must be verified (a system, anisotropic, in the normal form), with rank A_u = 3 and
   every rank <= 4.

A failure of 1 means a bug or a transcription error: fix it, re-run as -v2, count nothing from
that job.

## Exploratory, with the decision rule

Guesses (low confidence): no SAT. The nine UNSAT answers of m42a and m42b all came at 65 to 95
percent of a 200 to 277 s budget, and at t = 6 the analogous shape needed up to 24 minutes for most
classes and 74 for the last (jobs m33, m34, m36, m37). So with 14 to 15 minutes: batch b (d <= 1,
including the two pair orbits with UNSAT answers) 4 to 9 of 11 UNSAT; batch c (d = 1) 2 to 6 of 9;
batch a (mostly d >= 2) 0 to 4 of 9. If m45 has reported by the time m47 is queued, its
proportion at 10.4 minutes replaces these guesses.

Rule:
- Every class of (B6) UNSAT, over m42a, m42b, m45, m47 and any follow-up, with every graded check
  held: **no anisotropic system with t = 7 and dim V = 9 has an element of rank exactly 3 in (B6)**,
  computer-assisted.
- Classes still UNKNOWN after m47: do not escalate blindly. Write down how long the solved classes
  took; a further pass only if it is at most 30 minutes per class and fits the queue; otherwise split
  the class by hand (a second fixed matrix, as Lemma 71 at t = 6) or find the hand facts of a34.md.
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
