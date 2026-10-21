# Job m72: predictions, written 2026-10-21 ~10:45Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m72 (cube_groups/m72.py) re-runs the 80 split instances of (B6) that job m70 left open, under
m70-predictions.md's rule for 1 to 30 open in a class, then splits two more classes of (B6) with
d = 0 at t = 7 and dim V = 9 (Proposition 33, notes/a52.md; counts by job m66). Everything but the
lists, the plan's re-run entries and the checks of the 80 is m69.py, imported unchanged.

- **m72a:** the 43 open instances of o004_c000 (10), o006_c000 (7), o008_c004 (12) and o003_c004
  (14), all of rank 0 on X_1 with Lemma 93 (b), each 300 s of CaDiCaL, then 300 s of XOR if open;
  then the split of o012_c009 (d = 0, sweep UNSAT: 1200 instances of rank 1 and 2).
- **m72b:** the 37 of o003_c002 (20) and o003_c003 (17), the same way; then the split of o012_c004
  (d = 0, sweep UNSAT: 1840).
- m69's pace rule (m70's median UNSAT wall was 1.02 to 1.12 s) asks for 4 or 5 classes per group.
  m72 takes one tail class per group because the re-runs may need up to 215 (a) and 185 (b)
  minutes of CaDiCaL at worst; this is a deliberate departure, written down here before the run.
  Instances not reached are SKIPPED and stay open.
- m71a (the 21 re-runs of o004_c001 and o006_c001; o008_c002 and o010_c002) was still pending when
  m72 was written; m72 touches none of its classes.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the tail class, unchanged (m57's 14 checks with the planted control at t = 6
   in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank on
   X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u; the
   plan; hints 79 and units 49 on the first instance in both arms). The tail class is not closed,
   split elsewhere or re-run here.
2. The re-runs: each of the group's classes recomputed by m66.py passes the same class and root
   checks; the list has 43 (a) or 37 (b) entries, as many per class as m70 left open, all of rank 0;
   each recomputed root at k has m70's index, map, orbit size and rank on X_1, is admissible, and
   carries Lemma 93; hints 79 and units 49 + 21 in both arms; the first Lemma 93 instance = the
   plain one + 21 unit clauses.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93, Proposition 33 or the sweep rule): re-check by an independent brute force
   before any claim.

## Exploratory, with the decision rules

Guesses (low confidence unless said):

- **The 80: at least 74 UNSAT; at least 4 of the 6 classes empty: medium confidence.** m70a's 27
  re-runs of (B5) all closed (slowest 80.7 s); o006_c000, run at 20 s, closed 3 of the 10 roots that
  o004_c000 left open at 10 s (k = 58, 199, 523), so these look slow rather than hard. Against it:
  m61a's last 7 rank-0 instances needed 108 to 272 s.
- **o012_c009 and o012_c004 empty (high confidence):** all four d = 0 classes split so far were
  (m69a, m70a), every instance under 2.7 s.
- **Same index, same pace:** the open roots repeat by m66 index within a pair orbit (o004_c000 and
  o006_c000 share 7 of their indices; o003_c002, c003 and c004 share 6 among all three). Guess: for
  re-runs at the same index in two classes of the same pair, the CaDiCaL walls are within a factor
  of 3 of each other for at least two thirds of such pairs (read from grade.json "rows").
- **Re-runs take under 60 minutes in each group: 50/50. No SKIPPED instance: about 70% in each.**
- **Median UNSAT wall at most 3 s in both tail classes (high confidence).**

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary. For the six named classes that means all of the class's re-runs UNSAT (with m70's).
- **Any re-run still open after both arms:** a third-matrix split by hand (m62's rule; these are
  all rank 0 on X_1, so the split is over A_(v_2) with Lemma 93 (b) kept).
- **1 to 30 open in a tail class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next
  job. **More than 30:** read them by rank first.
- **Pace:** median UNSAT wall at most 3 s: the next (B6) jobs keep 4 or 5 classes per group.
  Above 8 s anywhere: re-estimate the cost of the rest of the (B6) split and look for a hand
  reduction before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
