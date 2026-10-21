# Job m48 (m48a, m48b, m48c): predictions, written 2026-10-20 ~06:00Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m48.py (Apache-2.0), which
runs m42.py unchanged (the m42.py that jobs m42c and m42d ran) and reuses m46.py's tables, with
sat_aniso.py from the repository. Setting: notes/a27.md (Lemma 83), notes/a33.md and notes/a35.md
(the results of jobs m42c and m42d).

## Why this job

Job m42d (2026-10-20 03:46 to 05:15 UTC) solved the second half of (B5): of its 210 classes of
A_u, 159 were UNSAT and 51 UNKNOWN. The undecided classes had budgets of about 40 to 97 s, four of
them 107, 142, 165 and 480 s. The decision rule of m42-predictions.md says: "UNKNOWN or SKIPPED
classes: one more job with at least 3 times the budget each". m48 is that job for these 51
classes, as m46 is for m42c's 42.

    m48a, m48b, m48c   the 51 names sorted and dealt round-robin, 17 each; 156 minutes per job,
                       at most 15 minutes per class

Each class gets an equal share of what is left (about 9.2 minutes, at least 3 times its m42d
budget for every class except o016_c024, whose 480 s would need 24 minutes).

## Not queued yet

Staged in compete-staged/m48a-c, not queued, in the run that wrote it: job m46 (the same kind of
3x pass on m42c's 42 classes) was queued in the same run and has not reported, and the shared
2-slot queue is used by every field. Rule: queue m48 as designed if m46 closes at least half of
its 42 classes; if it closes fewer, do not queue m48 and turn to the hand facts of a34.md / a35.md
(x0 not in Im A_u in (B5); the d = 3 classes) or a second fixed matrix.

## Graded (each must hold)

1. m48.py --part check: m42.py's classification of (B5), recomputed with the same code and seeds,
   has 420 classes with m46.py's per-pair counts (as m42c and m42d found); the 49 pairs are as in
   m46.PAIR_R; each of the 51 names has the representative that m42d recorded, with kernel X_1 and
   image R of its pair; every name lies in m42d's half (index 1 of 2, 210 classes); no name is
   one of m46's 42; the probe instance has 111 hint conditions and consistent unit clauses; the
   batches split the 51 names 17 + 17 + 17.
2. Any SAT must be verified (a system, anisotropic, in the normal form), with rank A_u = 3 and
   every rank <= 4.

A failure of 1 means a bug or a transcription error: fix it, re-run as -v2, count nothing from
that job.

## Exploratory, with the decision rule

Guesses (low confidence): no SAT. In m42d, 159 UNSAT answers came in 2.2 to 51 s (most under 15 s), so the open classes are the hard tail. With about 9 minutes
each: 20 to 35 of 51 UNSAT in all. The five classes with d = 3 (pairs 0, 0, 1, 31, 33; A_u^2 = 0)
are the most likely to stay open: all 13 classes of (B5) and (B6) with d = 3 have stayed open at
every budget tried so far. The six open classes in the kind-L pair orbits (3, 7, 43; x0 in Im A_u)
are the next most likely to close, as 91 of the 97 kind-L classes closed in the 40 s pass.

Rule:
- Every class of (B5) UNSAT, over m42c, m42d, m46, m48 and any follow-up, with every graded check
  held: **no anisotropic system with t = 7 and dim V = 9 has an element of rank exactly 3 in
  (B5)**, computer-assisted.
- Classes still UNKNOWN after m48: no blind escalation. Write down the times of the solved
  classes first; then either a hand split (a second fixed matrix, as Lemma 71 at t = 6) or the
  hand facts of a34.md and a35.md.
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
