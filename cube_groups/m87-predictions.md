# Job m87: predictions, written 2026-10-22 ~07:50Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m87 (cube_groups/m87.py) re-runs the 45 split instances of (B6) that jobs m85b, m86a and m86b
left open in their tails at their 10 to 20 s budgets, each with 5 minutes of CaDiCaL and then, only
if still open, 5 of XOR (the rule in m85-predictions.md and m86-predictions.md for 1 to 30 open in
a class). After them it splits two more classes of (B6) per group, all four with d = 2 and an open
rank-0 sweep (job m64a: UNKNOWN at 150 s). Everything but the lists, the plan and the check of the
45 is m69.py, imported unchanged; m87.py is m86.py with new lists and two tails per group (m69a ran
three).

- **m87a:** the 20 of o010_c001 (19 of rank 0 on X_1, with Lemma 93 (b), and one of rank 2,
  a0152, without it), then o003_c000 (|G| = 1536, 1599 orbits: 255, 896, 448 of rank 0, 1, 2) and
  o005_c000 (|G| = 512, 1913: 135, 920, 858).
- **m87b:** the 15 of o010_c008 and the 10 of o005_c002 (all of rank 0), then o003_c001 (|G| =
  1536, 1599: 255, 896, 448) and o005_c001 (|G| = 512, 1913: 135, 920, 858).

o005_c003 (|G| = 512, 1961: 135, 944, 882), the last class of (B6) not yet split, is split by job
m88 beside this one (m88-predictions.md). The rank-2 instance a0152 had a 10 s budget at the start of m86a's tail
and its record shows a wall of 81.21 s; how the extra time arose is not known (the host is
shared), and it is re-run here like the others.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's two tail classes, unchanged: m57's 14 checks with the planted
   control at t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit
   counts by rank on X_1 equal to m66's run; every root admissible, of its rank, distinct with its
   sum with A_u; the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first in each
   class); hints 79 and units 49 on the first instance in both arms; the Lemma 93 instance equal
   to the plain one plus exactly 21 negative unit clauses, in both arms.
2. m87's own: the three named classes against m66's run and their roots recomputed (index, map,
   rank on X_1, orbit size equal to what m85b and m86 recorded); 20 re-runs in group a (19 of rank
   0, 1 of rank 2) and 25 in group b (all of rank 0), as many per class as m85b and m86 left open;
   Lemma 93 (b) on each of rank 0 and on no other; hints 79 and units 70 on the first of rank 0,
   and units 49 on the one of rank 2, in both arms; the tails not among the 39 classes closed by
   the split and its re-runs or the three re-run here.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses. Every leftover re-run with 5 minutes in each arm so far has closed: 324 of 324 (m69a 1,
m70a-v2 27, m71a 21, m72 80, m73 19, m78r 1, m80r 7, m82 42, m83 53, m85a 12, m85b 12, m86 49), one
of them only in the XOR arm (m70a-v2); the slowest by CaDiCaL took under 245 s (m72). The last 61
took 13.61 to 129.54 s; both guesses of "slowest at most 120 s" missed (120.16 s in m85b, 129.54 s
in m86b), so the bound is raised here:

- **All 45 UNSAT within their 5 minutes of CaDiCaL: about 80%.**
- **o010_c001, o010_c008 and o005_c002 all empty after this job: about 80%.** If they are, every
  class of (B6) with d = 1 is empty.
- **Slowest of the 45 at most 180 s: about 70%.**
- **In each of the four tails: some rank-0 instances open (about 90% per class; about 10 to 40
  for o003_c000 and o003_c001, 5 to 25 for o005_c000 and o005_c001, low confidence); the class
  empty after this one pass (about 5% each); median UNSAT wall at most 3 s (high confidence).**
- **At least one open instance of rank 1 or 2 in at least one of the four tails: about 60%.** (Of
  the three classes with d = 2 split before with an open sweep, o004_c001 and o006_c001 left 2 and
  1 of rank 1 open, o005_c002 none; o010_c001, with d = 1, left one of rank 2.)
- **No SKIPPED instance: about 75% per group.** Each group has about 20 minutes of re-runs at the
  recent pace and 3512 split instances, at about 1.35 to 1.5 s each in m85b and m86 (about 80 to
  90 minutes), so about 100 to 110 of the 150 minutes.
- No guess on repeated m66 indices: two such guesses missed in a row (m84a, m85a), a third held
  (m86a: 10 of o010_c001's 19 open rank-0 indices were open in o010_c000, against "at least 5"),
  and m85b's missed (0 of 15). Overlaps are reported, not predicted.

Rules:

- **A named class with all its instances UNSAT:** it is empty, (B6) goes up by one, the next
  corollary. The same for a tail with all split instances UNSAT.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.
- **1 to 30 open in a tail (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL, then
  5 of XOR, in the next job. **More than 30:** read them by rank and by place in m66's order before
  queueing more; if they are all of rank 0 and not SKIPPED, re-run them in two jobs of at most 30.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
