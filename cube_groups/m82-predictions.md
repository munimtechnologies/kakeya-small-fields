# Job m82: predictions, written 2026-10-21 ~23:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m82 (cube_groups/m82.py) re-runs the 42 split instances of (B6) that jobs m79a and m79b left
open at their 10 to 20 s budgets, each with 5 minutes of CaDiCaL and then, only if still open, 5 of
XOR (m79-predictions.md's rule for 1 to 30 open in a class), and then splits one more class of
(B6) per group with d = 1 and an open rank-0 sweep (job m64a), as m79 and m81 do. Everything but the
lists, the plan and the check of the 42 is m69.py, imported unchanged.

- **m82a:** the 21 of o008_c000 (19 of rank 0 on X_1 with Lemma 93 (b), 2 of rank 1: a0619 and
  a0658), then o010_c003 (|G| = 384, 1975 orbits: 135, 920, 920 of rank 0, 1, 2).
- **m82b:** the 7 of o008_c001 and the 14 of o008_c003 (all of rank 0), then o010_c005 (|G| = 384,
  1975: 135, 920, 920).

**Departure, written before queueing.** m81-predictions.md keeps m81b staged until m79 and m81a are
graded. m79 is graded and met its pace rule in all three classes (median UNSAT wall 1.12, 1.07 and
1.12 s; 21, 7 and 14 open, each at most 30). m81a has not reported. m81b is queued now anyway,
with m82a and m82b (four pending with m81a), because m79 already ran three classes of the same kind
(d = 1, open sweep) at that pace. The two tails of m82 are queued under the same reasoning. If m81a
breaks the pace rule, its result and these still count, but nothing more of this kind is queued
before a look for a hand reduction.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's tail class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses, in both arms.
2. m82's own: the named classes against m66's run and their roots recomputed (index, map, rank on
   X_1, orbit size equal to what m79 recorded); the 21 per group, with 2 of rank 1 in group a and
   none in group b, as many per class as m79 left open; Lemma 93 (b) exactly on the rank-0 ones;
   hints 79 and units 70 on the first rank-0 one, units 49 on the first rank-1 one, in both arms;
   the tail not among the 27 classes closed by the split nor among the five split by m79 and m81.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses. Every leftover re-run with 5 minutes in each arm so far has closed: 156 of 156 (m69a 1,
m70a-v2 27, m71a 21, m72 80, m73 19, m78r 1, m80r 7), one of them only in the XOR arm (m70a-v2);
the slowest by CaDiCaL took under 245 s (m72, as a62.md records it):

- **All 42 UNSAT within their 5 minutes of CaDiCaL: about 80%.**
- **o008_c000, o008_c001 and o008_c003 all empty after this job: about 75%.**
- **Slowest of the 42 at most 120 s: about 65%.**
- **No XOR arm needed: about 80%.**
- **In o010_c003 and o010_c005: at most 2 open instances of rank 1 or 2 per class (about 80%),
  some rank-0 instances open (about 80%; about 5 to 35 per class, low confidence), the class empty
  after this one pass (about 15% each), median UNSAT wall at most 3 s (high confidence).**
- **No SKIPPED instance: about 80% per group.** The 21 re-runs at about 60 s each take about 21
  minutes and the 1975 instances about 50 (m79b took 48 minutes for 1975), well inside the 150.

Rules:

- **A named class with all its instances UNSAT:** it is empty, (B6) goes up by one, the next
  corollary (Corollary 99 on). The same for a tail with all split instances UNSAT.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.
- **1 to 30 open in a tail (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL, then
  5 of XOR, in the next job (this file's pattern). **More than 30:** read them by rank and by place
  in m66's order before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
