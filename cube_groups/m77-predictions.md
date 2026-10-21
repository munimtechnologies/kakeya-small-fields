# Job m77: predictions, written 2026-10-21 ~14:40Z before it runs

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m77 (cube_groups/m77.py) splits the last two classes of (B6) at t = 7 and dim V = 9 with d = 1
and a UNSAT rank-0 sweep by the second matrix A_(v_1) (Proposition 33, notes/a52.md; counts by job
m66; sweeps by job m64a). By Lemma 93 (a) only the split instances of rank 1 and 2 on X_1 are
needed. Everything but the lists is m69.py, imported unchanged.

- **m77a:** o009_c001 (d = 1, |G| = 192, 3839 orbits: 1792 of rank 1 and 1792 of rank 2, so 3584
  instances).
- **m77b:** o009_c004 (d = 1, |G| = 192, 3839 orbits, the same counts: 3584 instances).
- No class of (B6) has an open split instance after m73a, so there are no re-runs. m73b (6 re-runs
  and three splits), m74 (the machine count of Proposition 34) and m76 (three splits) were pending
  when m77 was written; m77 touches none of their classes.
- m77 was written while four jobs were pending and is queued by a later run once fewer than four
  are pending (the habit: at most two new jobs with fewer than four pending). If it is queued with
  more pending, the departure is written here first.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run (255, 1792, 1792); every root admissible, of its rank, distinct with
   its sum with A_u; the plan; hints 79 and units 49 on the first instance in both arms.
2. m77's own check: no class split here is among the 18 classes closed by the split or the 7 in
   flight in m73b and m76.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses:

- **Both classes empty: medium-high confidence.** Every class with d = 1 and a UNSAT sweep split so
  far (o009_c008 in m69b, o009_c003 and o007_c001 in m73a) was UNSAT in every instance, the
  slowest 4.18 s; m73b's three and m76a's two had not reported.
- **Median UNSAT wall at most 3 s in each class (high confidence).** m72 and m73a: 1.27 s.
- **No SKIPPED instance in either group: about 80%.** At m73a's pace (1.31 s per instance with
  overhead) each group needs about 78 minutes of the 150; |G| = 192 is the smallest group of any
  class split so far, so the instances may be no faster than those of the |G| = 384 classes.
- **Same index, same pace:** o009_c001 and o009_c004 have the same |G| and orbit counts. Guess:
  their slowest ten instances share at least five m66 indices (low confidence; read from the rows
  and m77_reps.json).

Rules:

- **All split instances of a class UNSAT:** the class is empty, (B6) goes up by one, the next
  corollary (Corollary 87 on, after any that m73b and m76 earn first).
- **1 to 30 open in a class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next job.
  **More than 30:** read them by rank first.
- **Pace:** median UNSAT wall at most 3 s: the next (B6) jobs keep about 3500 to 4600 split
  instances per group. Above 8 s anywhere: re-estimate the cost of the rest of the (B6) split and
  look for a hand reduction before queueing more. After m77 every open class of (B6) has an open
  sweep, so its rank-0 instances (135 to 256 per class) must be run too: the next jobs plan
  about 2500 instances per group when a class's rank-0 instances are included.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.

## Addendum, 2026-10-21 ~16:10Z, written when m77 was queued and before it ran

- Since this file was written, m73b reported (34 of 34 graded checks held; o010_c002, o007_c004,
  o007_c007 and o009_c000 empty, Corollaries 87 to 90, notes/a64.md; median 1.07 to 1.12 s and
  1.12 s per split instance with overhead) and m74 reported (15 of 15 held). m76b stopped when its
  container vanished before setup ran, so it is re-queued unchanged as m76b-v2; m76a had not
  reported.
- m77a and m77b are queued with two jobs pending (m76a and m76b-v2), so four are pending in all:
  within the habit (two new, fewer than four pending before), no departure.
- The classes split in m73b are now closed rather than in flight; m77's lists still name them
  among the 25 classes it must not split, so its own check is unchanged. Nothing above changes:
  every guess and rule stands as written. Corollary numbers now start at 91.
