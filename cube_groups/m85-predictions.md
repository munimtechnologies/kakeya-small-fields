# Job m85: predictions, written 2026-10-22 ~04:10Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m85 (cube_groups/m85.py) re-runs the 24 split instances of (B6) that jobs m83a and m83b left
open in their tails at their 10 to 20 s budgets, each with 5 minutes of CaDiCaL and then, only if
still open, 5 of XOR (the rule in m83-predictions.md for 1 to 30 open in a class). After them it
splits one more class of (B6) per group with d = 1 and an open rank-0 sweep (job m64a: UNKNOWN at
150 s), as m83 does. Everything but the lists, the plan and the check of the 24 is m69.py,
imported unchanged; m85.py is m83.py with new lists.

- **m85a:** the 12 of o010_c004 (all of rank 0 on X_1, with Lemma 93 (b)), then o010_c007
  (|G| = 384, 2023 orbits: 135, 944, 944 of rank 0, 1, 2).
- **m85b:** the 12 of o010_c006 (all of rank 0), then o010_c008 (|G| = 384, 2023: 135, 944, 944).

m84a and m84b (o009_c007 and o010_c000) are still in the queue; their leftovers, and the split of
o010_c001 (the last class with d = 1), go to the next job.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's tail class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses, in both arms.
2. m85's own: the two named classes against m66's run and their roots recomputed (index, map, rank
   on X_1, orbit size equal to what m83 recorded); 12 re-runs per group, all of rank 0, as many
   per class as m83 left open; Lemma 93 (b) on each; hints 79 and units 70 on the first, in both
   arms; the tail not among the 34 classes closed by the split, the two re-run here, or the two
   split by m84.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses. Every leftover re-run with 5 minutes in each arm so far has closed: 251 of 251 (m69a 1,
m70a-v2 27, m71a 21, m72 80, m73 19, m78r 1, m80r 7, m82 42, m83 53), one of them only in the XOR
arm (m70a-v2); the slowest by CaDiCaL took under 245 s (m72), and m83's slowest took 118.37 s (a
rank-0 one of o010_c003):

- **All 24 UNSAT within their 5 minutes of CaDiCaL: about 80%.**
- **o010_c004 and o010_c006 both empty after this job: about 80%.**
- **Slowest of the 24 at most 120 s: about 65%.**
- **In o010_c007 and o010_c008 (the same orbit counts as o010_c004): no open instance of rank 1
  or 2 (about 80% per class); some rank-0 instances open (about 90%; about 5 to 25 per class, low
  confidence); the class empty after this one pass (about 5% each); median UNSAT wall at most 3 s
  (high confidence).**
- **Repetition by m66 index (low confidence, about 50%):** at least half of the open instances of
  o010_c007 have an m66 index among the 12 open in o010_c004 (512, 1024, 3072, 4096, 5120, 7168,
  9216, 20480, 21504, 27648, 37888, 40448); the same for o010_c008. m66's index depends on each
  class's basis of R, so this is a pattern to test, not an expected identity.
- **No SKIPPED instance: about 85% per group.** 12 re-runs at about 20 to 120 s take about 5 to 20
  minutes and the tail about 50 (m83a: 26 re-runs and 2023 in 64 minutes), well inside the 150.

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
