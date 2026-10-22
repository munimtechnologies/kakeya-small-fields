# Job m89: predictions, written 2026-10-22 ~10:00Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m89 (cube_groups/m89.py) re-runs the 49 split instances of (B6) that job m87b left open in its
tails at 10 to 20 s: 32 of o003_c001 (all of rank 0 on X_1, with Lemma 93 (b)) and 17 of
o005_c001 (16 of rank 0, and a0042 of rank 1 without it). Each gets 5 minutes of CaDiCaL and then,
only if still open, 5 of XOR. o003_c001 left more than 30, so under the rule in
m87-predictions.md (all of rank 0, none SKIPPED) its 32 run in two jobs of 16, and o005_c001's 17
are shared out beside them:

- **m89a:** o003_c001 a0042 to a0817 (16), then o005_c001 a0042 to a1214 (9, a0042 of rank 1).
- **m89b:** o003_c001 a0823 to a1580 (16), then o005_c001 a1450 to a1905 (8).

No class is split. Everything but the lists, the plan and the check is m69.py, imported unchanged.
m69.check needs at least one tail class, so m89.py has its own check: m57.py's 14 checks as
m69.check runs them, then the re-runs checked as m87.py checks its 45. This is a departure from
m87 and m88, written down here before it runs.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57's 14 checks with the planted control at t = 6 in both arms.
2. Both classes of the group against m66's run (structure, |G| = Proposition 33 (c), |Adm| = (a),
   orbit counts by rank on X_1) and their roots recomputed (every root admissible, of its rank,
   with its m66 index, distinct with its sum with A_u).
3. The list: both groups together are exactly m87b's 49 open instances, once each (32 and 17,
   matching m87b's 1599 - 1567 and 1913 - 1896); 16 + 9 in group a and 16 + 8 in group b; ranks
   24 + 1 and 24 + 0; neither class among the 41 closed by the split and its re-runs. Each re-run's
   name, index, map, rank on X_1 and orbit size equal to what m87b recorded; Lemma 93 (b) on each
   of rank 0 and on no other.
4. The plan: only the re-runs, CaDiCaL then XOR, each at the full 300 s cap.
5. Hints 79 and units 70 on the first of rank 0, units 49 on the one of rank 1 (group a), in both
   arms; the Lemma 93 instance equal to the plain one plus exactly 21 negative unit clauses.
6. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Every leftover re-run with 5 minutes in each arm so far has closed: 349 of 349, one of them only in
the XOR arm (m70a-v2); the slowest by CaDiCaL took under 245 s (m72), the last 86 took 13.61 to
129.54 s. o003_c001's 32 ran at only 10 s in m87b (o005_c001's at 20 s), so they were cut off
earlier than most leftovers so far.

- **All 49 UNSAT within their 5 minutes of CaDiCaL: about 80%.**
- **o003_c001 and o005_c001 both empty after m89a and m89b: about 80%.**
- **Slowest of the 49 at most 180 s: about 70%.**
- **a0042 of o005_c001 (rank 1) UNSAT within 60 s: about 60%.** (It stopped at 10 s; the
  rank-1 and rank-2 leftovers so far closed by re-run, but their times were not tabulated apart.)
- **Median CaDiCaL wall of o003_c001's 32 below that of o005_c001's 16 of rank 0: about 50%** (a
  coin toss, recorded so that it is graded rather than read after the fact).
- No guess on repeated m66 indices. Observed before m89 ran: every one of o005_c001's 16 open
  rank-0 indices is among o003_c001's 32 (with the same mask at some indices and a different one
  at others, since the two pair orbits have their own bases of R), and 11 of o003_c001's 32 were
  open in o010_c001 (m86a).

Rules:

- **A class whose leftovers are all UNSAT across m89a and m89b:** it is empty, (B6) goes up by
  one, the next corollary. One group alone does not empty o003_c001 or o005_c001.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count its class as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
