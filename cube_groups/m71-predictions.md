# Job m71: predictions, written 2026-10-21 ~09:10Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m71 (cube_groups/m71.py) re-runs the 21 split instances of (B6) that job m69b left open, under
m69-predictions.md's rule for 1 to 30 open in a class, then continues the second-matrix splits of
(B6) at t = 7 and dim V = 9 (Proposition 33, notes/a52.md; counts by job m66). Everything but the
lists, the plan's first 42 entries and the checks of the 21 is m69.py, imported unchanged.

- **m71a:** the 21 open instances of o004_c001 (13: 2 of rank 1 on X_1, 11 of rank 0 with Lemma 93
  (b)) and o006_c001 (8: 1 of rank 1, 7 of rank 0), rank 1 first, each 300 s of CaDiCaL, then 300 s
  of XOR if open; then the splits of o008_c002 and o010_c002 (d = 1, sweep open: 1021 each, the 69
  of rank 0 with Lemma 93 (b)). 2042 split instances.
- m69's pace rule (median UNSAT wall at most 3 s; m69b had 1.22 to 1.42 s) asks for 4 or 5 classes
  per group. m71a takes 2 because the 21 re-runs may need up to 210 minutes at worst; this is a
  deliberate departure, written down here before the run. Instances not reached are SKIPPED and
  stay open.
- m70a-v1 was stopped by its host 4 minutes into its solve part (exit 143) after its check passed;
  no split instance had finished, so nothing of it is counted. It is re-run unchanged as m70a-v2
  (same code, copied into this run's jobs/ and checked line for line), under m70-predictions.md as
  written before v1 ran. m70b-v1 (o008_c004, o003_c002/3/4) is still pending; m71 splits none of
  m70's classes.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the two tail classes, unchanged (m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan; hints 79 and units 49 on the first instance in both arms; the first Lemma 93 instance
   = the plain one + 21 unit clauses, in both arms). Neither tail class is closed or split before.
2. The 21: o004_c001 and o006_c001 recomputed by m66.py pass the same class and root checks; the
   list has 13 + 8 = 587 - 574 + 587 - 579 entries, 3 of rank 1 first, 18 of rank 0; each
   recomputed root at k has m69b's index, map, orbit size and rank on X_1, is admissible, and has
   Lemma 93 exactly when of rank 0; hints 79 and units 49 (or 49 + 21) in both arms; the first
   Lemma 93 instance = the plain one + 21 unit clauses.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93, Proposition 33 or the sweep rule): re-check by an independent brute force
   before any claim.

## Exploratory, with the decision rules

Guesses (low confidence unless said):

- **The 21: at least 18 UNSAT; o004_c001 and o006_c001 both empty: 50/50; at least one empty:
  yes, medium confidence.** a561 (open at 11.4 s) closed in 1.37 s in m69a, and m63a closed 24 of
  24 re-opened rank-0 instances with Lemma 93 in at most 92 s; but m61a's last 7 kind-L instances
  (rank 0) needed 108 to 272 s, and these were open at 10 to 20 s.
- **The same 7 roots (k = 152, 210, 320, 334, 354, 426, 545, all rank 0) were open in both
  classes in m69b; guess: they close or stay open together** (both or neither UNSAT for at least 6
  of the 7 pairs).
- **o008_c002 and o010_c002: at least 990 of 1021 UNSAT each; neither empty: likely (about 70%).**
  m69b's d = 2 classes with rank-0 instances left 13 and 8 open; o009_c008 (d = 1, sweep UNSAT, no
  rank-0 instances) closed all 696.
- **Median UNSAT wall at most 3 s in both tail classes; the rank-0 instances have a higher median
  than the rank 1 and 2 ones.**
- **No SKIPPED instance: about 70%** (if the 21 take over 60 minutes, the tails get less than 10 s
  each only at the end).

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary. For o004_c001 and o006_c001 that means all 21 of the class's re-runs UNSAT (with
  m69b's 574 and 579).
- **Any of the 21 still open after both arms:** a third-matrix split by hand (m62's rule), and
  Lemma 94 (the clausal form of "rank at most 1 on X_1") is designed for the rank-1 ones.
- **1 to 30 open in a tail class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next
  job. **More than 30:** read them by rank first; rank-0 ones get a third-matrix split by hand,
  rank 1 or 2 ones a 60 s pass first.
- **Pace:** median UNSAT wall at most 3 s: the next (B6) jobs keep 4 or 5 classes per group.
  Above 8 s anywhere: re-estimate the cost of the rest of the (B6) split and look for a hand
  reduction before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
