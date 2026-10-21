# Job m73: predictions, written 2026-10-21 ~11:50Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m73 (cube_groups/m73.py) re-runs the 19 split instances of (B6) that job m71a left open, under
m71-predictions.md's rule for 1 to 30 open in a class, then continues the second-matrix splits of
(B6) at t = 7 and dim V = 9 (Proposition 33, notes/a52.md; counts by job m66) with five classes of
d = 1 whose rank-0 sweep (job m64a) was UNSAT, so that only their instances of rank 1 and 2 on X_1
are needed (Lemma 93 (a)). Everything but the lists, the plan's first entries and the checks of
the 19 is m69.py, imported unchanged.

- **m73a:** the 13 open instances of o008_c002 (all of rank 0, with Lemma 93 (b)), each 300 s of
  CaDiCaL, then 300 s of XOR if open; then the splits of o009_c003 (1200) and o007_c001 (1344).
- **m73b:** the 6 open instances of o010_c002 (rank 0, Lemma 93 (b)), as above; then the splits
  of o007_c004 (1344), o007_c007 (1344) and o009_c000 (1888).
- m69's pace rule asks for 4 or 5 classes per group; it was set when classes had 500 to 1000 split
  instances. These have 1200 to 1888, so m73a takes 2 classes (2544 instances) and m73b 3 (4576).
  This is a deliberate departure, written down here before the run: about 2500 to 4600 instances
  per group is what m70b (3288 in 81 min) and m71a (2042 + 21 re-runs in 75 min) did. Instances
  not reached are SKIPPED and stay open.
- m72a and m72b (the 80 re-runs of m70 and the splits of o012_c009, o012_c004) are still pending;
  m73 splits none of their classes.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the tail classes, unchanged (m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan, no tail instance of rank 0; hints 79 and units 49 on the first instance in both
   arms). No tail class is closed, split before, or in m72.
2. The 19: o008_c002 and o010_c002 recomputed by m66.py pass the same class and root checks; the
   list has 13 + 6 = (1021 - 1008) + (1021 - 1015) entries, all of rank 0; each recomputed root
   at k has m71a's index, map, orbit size and rank on X_1, is admissible, and carries Lemma 93;
   hints 79 and units 49 + 21 in both arms; the first Lemma 93 instance = the plain one + 21 unit
   clauses.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93, Proposition 33 or the sweep rule): re-check by an independent brute force
   before any claim.

## Exploratory, with the decision rules

Guesses (low confidence unless said):

- **The 19: at least 17 UNSAT (medium confidence); o008_c002 and o010_c002 both empty: about
  60%.** m71a closed all 21 rank-0 re-runs of o004_c001 and o006_c001 by CaDiCaL within 240 s, and
  m70a closed 27 of 27 (B5) re-runs; but these 19 come from d = 1 classes with a different group
  (|G| = 768), and no d = 1 rank-0 re-run has been graded yet.
- **The 6 roots of o010_c002 (k = 34, 103, 151, 757, 769, 1015) are open at the same k, with the
  same m66 index and orbit size, in o008_c002; guess: they close or stay open together** (both or
  neither UNSAT for at least 5 of the 6), and their CaDiCaL times are within a factor of 2 of each
  other for at least 4 of the 6. In m71a the 7 shared roots of o004_c001 and o006_c001 were all
  UNSAT in both, with times within a factor of 2 for 7 of 7.
- **Each of the five tail classes empty: likely (about 80% each); all five empty: about 60%.**
  Every class split so far whose sweep was UNSAT (o011_c003, o011_c004, o012_c011, o009_c008,
  o011_c002: 512 + 512 + 510 + 696 + 924 = 3154 instances of rank 1 and 2) closed every instance.
- **Median UNSAT wall at most 3 s in every tail class** (m69 to m71: 1.0 to 1.4 s).
- **No SKIPPED instance: m73a about 85%, m73b about 65%** (m73b has 4576 instances; at 1.45 s
  each that is about 111 minutes before its re-runs).

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary. For o008_c002 and o010_c002 that means all of the class's re-runs UNSAT (with m71a's
  1008 and 1015).
- **Any of the 19 still open after both arms:** a third-matrix split by hand (m62's rule: rank 0,
  split over A_(v_2), keeping Lemma 93 (b)).
- **1 to 30 open in a tail class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next
  job. **More than 30:** read them by rank first; rank 1 or 2 ones get a 60 s pass first.
- **SKIPPED instances:** they are not results; they go first in the next split job of that class.
- **Pace:** median UNSAT wall at most 3 s: keep about 2500 to 4600 instances per group. Above 8 s
  anywhere: re-estimate the cost of the rest of the (B6) split and look for a hand reduction before
  queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
