# Job m83: predictions, written 2026-10-22 ~01:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m83 (cube_groups/m83.py) re-runs the 53 split instances of (B6) that jobs m81a, m81b, m82a and
m82b left open in their tails at their 10 to 20 s budgets, each with 5 minutes of CaDiCaL and then,
only if still open, 5 of XOR (the rule in m81-predictions.md and m82-predictions.md for 1 to 30 open
in a class). After them it splits one more class of (B6) per group with d = 1 and an open rank-0
sweep (job m64a), as m82 does. Everything but the lists, the plan and the check of the 53 is
m69.py, imported unchanged.

- **m83a:** the 11 of o009_c005 and the 15 of o010_c003 (all 26 of rank 0 on X_1, with Lemma 93
  (b)), then o010_c004 (|G| = 384, 2023 orbits: 135, 944, 944 of rank 0, 1, 2).
- **m83b:** the 16 of o009_c006 (14 of rank 0; a0003 of rank 1; a3209 of rank 2) and the 11 of
  o010_c005 (all of rank 0), then o010_c006 (|G| = 384, 1975: 135, 920, 920).

The rank-2 instance a3209 is the only one of rank 2 among the 53. Its first run used
156.8 s of wall time on a 10 s budget before the child stopped (m81b's stdout); the time over the
budget is not explained here and is not read as evidence either way.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's tail class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses, in both arms.
2. m83's own: the four named classes against m66's run and their roots recomputed (index, map, rank
   on X_1, orbit size equal to what m81 and m82 recorded); 26 re-runs in group a (all rank 0) and
   27 in group b (25, 1 and 1 of rank 0, 1 and 2), as many per class as m81 and m82 left open;
   Lemma 93 (b) exactly on the rank-0 ones; hints 79 and units 70 on the first rank-0 one, units 49
   on the first one of rank 1 or 2, in both arms; the tail not among the 30 classes closed by the
   split, the four re-run here, or the two split by m84.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses. Every leftover re-run with 5 minutes in each arm so far has closed: 198 of 198 (m69a 1,
m70a-v2 27, m71a 21, m72 80, m73 19, m78r 1, m80r 7, m82 42), one of them only in the XOR arm
(m70a-v2); the slowest by CaDiCaL took under 245 s (m72), and m82's slowest took 89.2 s:

- **All 53 UNSAT within their 5 minutes of CaDiCaL: about 75%.** (a3209 is the one I am least
  sure of.)
- **o009_c005, o009_c006, o010_c003 and o010_c005 all empty after this job: about 70%.**
- **Slowest of the 53 at most 120 s: about 55%.**
- **No XOR arm needed: about 75%.**
- **In o010_c004 and o010_c006: at most 2 open instances of rank 1 or 2 per class (about 80%),
  some rank-0 instances open (about 85%; about 5 to 35 per class, low confidence), the class empty
  after this one pass (about 10% each), median UNSAT wall at most 3 s (high confidence).**
- **No SKIPPED instance: about 75% per group.** The 26 or 27 re-runs at about 30 to 60 s each take
  about 15 to 30 minutes and the tail about 50 (m82b took 56 minutes for 21 re-runs and 1975),
  well inside the 150.

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
