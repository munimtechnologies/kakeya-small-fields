# Job m76: predictions, written 2026-10-21 ~13:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m76 (cube_groups/m76.py) splits three more classes of (B6) at t = 7 and dim V = 9 by the
second matrix A_(v_1) (Proposition 33, notes/a52.md; counts by job m66). All three had a UNSAT
rank-0 sweep in job m64a, so by Lemma 93 (a) only the split instances of rank 1 and 2 on X_1 are
needed. Everything but the lists is m69.py, imported unchanged.

- **m76a:** o009_c002 and o009_c009 (d = 1, |G| = 384, 2023 orbits each: 944 of rank 1 and 944
  of rank 2, so 1888 instances each, 3776 in all).
- **m76b:** o012_c001 (d = 0, |G| = 168, 3840 orbits: 1792 of rank 1 and 1792 of rank 2, 3584
  instances).
- No class of (B6) has an open split instance after m72, so there are no re-runs. m73 (19 re-runs
  and five splits) and m74 (the machine count of Proposition 34) were still pending when m76 was
  written; m76 touches none of their classes.
- **Departure, written down before queueing:** the habit is at most two new jobs with fewer than
  four pending. m76 is two new jobs with three pending (m73a, m73b, m74), so five will be pending.
  They are queued anyway because the classes are independent of m73 and m74 and the two compute
  slots would otherwise wait on the next run.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's classes, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run (and to Proposition 33 (d) for o012_c001: 3840); every root
   admissible, of its rank, distinct with its sum with A_u; the plan; hints 79 and units 49 on the
   first instance in both arms.
2. m76's own check: no class split here is among the 15 classes closed by the split or the 7 in
   flight in m73.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses:

- **All three classes empty: high confidence for o012_c001** (all six classes with d = 0 split so
  far, in m69a, m70a and m72, were UNSAT in every instance, the slowest 4.33 s); **medium-high for
  o009_c002 and o009_c009** (the only class with d = 1 and a UNSAT sweep split so far, o009_c008
  in m69b, was UNSAT in every instance; m73's five such classes had not reported).
- **Median UNSAT wall at most 3 s in each class (high confidence).** m72's tails: 1.27 s.
- **No SKIPPED instance in either group: about 85%.** At m72's pace (about 1.3 s per instance
  with overhead) group a needs about 82 minutes and group b about 78 of the 150.
- **Same index, same pace:** o009_c002 and o009_c009 have the same |G| and orbit counts. Guess:
  their slowest ten instances share at least five m66 indices (low confidence; read from the rows
  and m76_reps.json).

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary (Corollary 84 on).
- **1 to 30 open in a class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next job.
  **More than 30:** read them by rank first.
- **Pace:** median UNSAT wall at most 3 s: the next (B6) jobs keep about 3500 to 4600 split
  instances per group. Above 8 s anywhere: re-estimate the cost of the rest of the (B6) split and
  look for a hand reduction before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
