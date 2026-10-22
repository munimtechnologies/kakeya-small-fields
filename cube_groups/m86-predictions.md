# Job m86: predictions, written 2026-10-22 ~06:00Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m86 (cube_groups/m86.py) re-runs the 49 split instances of (B6) that jobs m84a, m84b and m85a
left open in their tails at their 10 to 20 s budgets, each with 5 minutes of CaDiCaL and then,
only if still open, 5 of XOR (the rule in m84-predictions.md and m85-predictions.md for 1 to 30
open in a class). After them it splits one more class of (B6) per group whose rank-0 sweep was open
(job m64a: UNKNOWN at 150 s). Everything but the lists, the plan and the check of the 49 is m69.py,
imported unchanged; m86.py is m85.py with new lists.

- **m86a:** the 14 of o009_c007 (all of rank 0 on X_1, with Lemma 93 (b)), then o010_c001, the
  last class with d = 1 not yet split (|G| = 192, 3839 orbits: 255, 1792, 1792 of rank 0, 1, 2).
- **m86b:** the 22 of o010_c000 and the 13 of o010_c007 (all of rank 0), then o005_c002, the first
  of the six open classes with d = 2 (|G| = 1024, 1069 orbits: 75, 520, 474).

o005_c002 is the smallest of the six d = 2 classes. 35 re-runs in one group is more than the 1 to
30 per class of the rule, but each class has at most 22, which is within it.

m85b (the 12 of o010_c006, then o010_c008) is still in the queue; its leftovers go to the next
job.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's tail class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses, in both arms.
2. m86's own: the three named classes against m66's run and their roots recomputed (index, map,
   rank on X_1, orbit size equal to what m84 and m85 recorded); 14 re-runs in group a and 35 in
   group b, all of rank 0, as many per class as m84 and m85a left open; Lemma 93 (b) on each;
   hints 79 and units 70 on the first, in both arms; the tail not among the 35 classes closed by
   the split, the three re-run here, or the two in m85b.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses. Every leftover re-run with 5 minutes in each arm so far has closed: 263 of 263 (m69a 1,
m70a-v2 27, m71a 21, m72 80, m73 19, m78r 1, m80r 7, m82 42, m83 53, m85a 12), one of them only in
the XOR arm (m70a-v2); the slowest by CaDiCaL took under 245 s (m72); m85a's 12 took 19.43 to
71.2 s.

- **All 49 UNSAT within their 5 minutes of CaDiCaL: about 80%.**
- **o009_c007, o010_c000 and o010_c007 all empty after this job: about 80%.**
- **Slowest of the 49 at most 120 s: about 60%.**
- **o010_c001 (the same |G| and orbit counts as o009_c007 and o010_c000, which left 14 and 22
  open): no open instance of rank 1 or 2 (about 75%); some rank-0 instances open (about 90%; about
  10 to 30, low confidence); the class empty after this one pass (about 5%); median UNSAT wall at
  most 3 s (high confidence).**
- **o005_c002 (d = 2; the two d = 2 classes split before with an open sweep, o004_c001 and
  o006_c001 in m69b, left 13 and 8 open, 11 and 7 of rank 0 and 2 and 1 of rank 1): some rank-0
  instances open (about 90%; about 5 to 25, low confidence); at least one open instance of rank 1
  or 2 (about 50%); the class empty after this one pass (about 5%); median UNSAT wall at most 3 s
  (high confidence).**
- **No SKIPPED instance: about 75% for m86a** (m84a's 3839 took 4962 s, plus about 10 minutes of
  re-runs, of the 150 minutes), **about 85% for m86b.**
- **Repetition by m66 index (low confidence, about 50%):** at least 5 of o010_c001's open rank-0
  instances sit at an m66 index also open in o010_c000 (512, 1536, 2560, 3584, 4608, 8192, 8704,
  9216, 10752, 12288, 13824, 23040, 24576, 25088, 27136, 27648, 28672, 33280, 37376, 41472,
  74752, 77312), the other class of pair orbit 10 with |G| = 192. m66's index depends on each
  class's basis of R, so this is a pattern to test, not an expected identity. (The two such
  guesses before this one both missed: 4 of 14 in m84a against "at least 5", 5 of 13 in m85a
  against "at least half".)

Rules:

- **A named class with all its instances UNSAT:** it is empty, (B6) goes up by one, the next
  corollary. The same for a tail with all split instances UNSAT.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.
- **1 to 30 open in a tail (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL, then
  5 of XOR, in the next job. **More than 30:** read them by rank and by place in m66's order before
  queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
