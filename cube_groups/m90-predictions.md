# Job m90: predictions, written 2026-10-22 ~12:50Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m90 (cube_groups/m90.py) re-runs the 32 split instances of (B6) that job m88a-v2 left open in
o005_c003 (d = 2) at 10 to 20 s: 16 of rank 0 on X_1 (with Lemma 93 (b)) and 16 of rank 1
(without it), none SKIPPED. Each gets 5 minutes of CaDiCaL and then, only if still open, 5 of XOR.
32 is more than 30, so under the rule in m88-predictions.md they run in two jobs of 16, split by
place in m66's order:

- **m90a:** a0015 to a0846 (11 of rank 1, 5 of rank 0).
- **m90b:** a0927 to a1960 (11 of rank 0, 5 of rank 1).

No class is split. m90.py is m89.py with new lists: the same plan (re-runs only), the same own
check (m57.py's 14 checks as m69.check runs them, then the re-runs as m87.py checks its 45) and
the same grade; everything else is m69.py, imported unchanged. Job m87a-v2 (o010_c001's 20
re-runs and the splits of o003_c000 and o005_c000) had not reported when this was written; it is
graded on its own against m87-predictions.md.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57's 14 checks with the planted control at t = 6 in both arms.
2. o005_c003 against m66's run (structure, |G| = 512 = Proposition 33 (c), |Adm| = 176126 = (a),
   orbit counts 135, 944, 882 by rank on X_1) and its roots recomputed (every root admissible, of
   its rank, with its m66 index, distinct with its sum with A_u).
3. The list: both groups together are exactly m88a-v2's 32 open instances, once each (1961 -
   1929); 16 in each group; ranks 5 + 11 in group a and 11 + 5 in group b; the class not among the
   43 closed by the split and its re-runs. Each re-run's name, index, map, rank on X_1 and orbit
   size equal to what m88a-v2 recorded; Lemma 93 (b) on each of rank 0 and on no other.
4. The plan: only the re-runs, CaDiCaL then XOR, each at the full 300 s cap.
5. Hints 79 and units 70 on the first of rank 0, units 49 on the first of rank 1, in both arms; the
   Lemma 93 instance equal to the plain one plus exactly 21 negative unit clauses.
6. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Every leftover re-run with 5 minutes in each arm so far has closed: 398 of 398; the slowest by
CaDiCaL took under 245 s (m72), the last 49 took 11.40 to 94.61 s. Those 49 were all of rank 0 but
one; here 16 are of rank 1, which run without Lemma 93 (b). That one, a0042 of o005_c001, closed in
14.21 s (m89a); earlier rank-1 leftovers also closed, but their times were not tabulated apart. 11 of the 16 of
rank 1 stopped at 10.01 s, the other 5 at 11.49 to 20.01 s; all 16 of rank 0 had a 20 s budget.

- **All 32 UNSAT within their 5 minutes of CaDiCaL: about 70%.**
- **o005_c003 empty after m90a and m90b (either arm): about 80%.**
- **Slowest of the 32 at most 180 s: about 60%.**
- **Median CaDiCaL wall of the 16 of rank 1 below that of the 16 of rank 0: about 50%** (a coin
  toss, recorded so that it is graded rather than read after the fact).
- No guess on repeated m66 indices. Observed before m90 ran: a0042 of o005_c003 has the same m66
  index (45), mask and orbit size as a0042 of o005_c001.
- Observed, not graded: in m88a-v2, a0767 (rank 0) ran 293.99 s of wall on a 20 s budget before it
  was stopped, as has happened before (m69.py notes 86 s on an 11.4 s budget). Its answer is
  UNKNOWN and counts as open; it is re-run here like the others.

Rules:

- **All 32 UNSAT across m90a and m90b:** o005_c003 is empty, (B6) goes up by one, the next
  corollary. One group alone does not empty it.
- **A re-run still open after both arms:** the first leftover of (B6) that did not close at 300 s.
  Write it down, do not count the class as empty, and look at a third-matrix split of that
  instance by hand before queueing anything for it.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
