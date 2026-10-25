# Job m107: predictions, written 2026-10-25 in the run that started at 05:27Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m106a, m106b and m106e came back (notes/a99.md). In m106e the six core cases and the four
k = 6 cases of o000_c000 were UNSAT with no anisotropy clause at all ("none"), in 6 to 56 s, and the
positive control was SAT. In m106a, 24 of the 28 open d = 2 cases were decided; four t2 cases of
type nil3 are still open. In m106b, anisotropy on N alone decided 33 of 37 cases of the d = 1 class
o007_c008 but only 5 of 36 in the two d = 0 classes, where 6 cases were SAT at "n".

Job m107 (cube_groups/m107.py; jobs m107a, m107b, m107c, m107e, m107f) imports m102.py to m106.py
unchanged. It splits the hand conditions of a case into twelve groups (H1-H4 from m42's hints, S1-S2
from m100's sweep, Z, X and C from m101, M, XE and CE from m102; table in m107.py). Every CNF keeps
the system (*) and m42's normal form. With all twelve groups it is m102's "relax" CNF, the "none"
CNF of m106e.

    m107a  the four open d = 2 cases at "n" (anisotropy on N), 900 s each
    m107b  half of the 88 cases with k(T(N)) > 4 of the three d = 3 classes (k = 6: 56, k = 8: 21,
    m107c  k = 10: 11), after the positive control at "none": each at "none", and at "n" if "none"
           is not UNSAT, 75 s each
    m107e  the six core cases; m107f the four k = 6 cases: the control with all groups, then for
           each case all twelve groups, then a deletion-minimal set of groups with the CNF still
           UNSAT, dropping in the order X, XE, CE, C, S2, S1, H4, H3, H2, H1, Z, M; 90 s per solve.
           A kept group is proven needed when dropping it gives a model verified outside the
           encoder (the system (*), the normal form, every kept group)

## Graded (each must hold)

- Unit tests pass (10 in test_m107) in each job. With all twelve groups the control's CNF has the
  same clause hash, clause count and variable count as m102's relax CNF; the groups add 24, 120,
  9, 9, 120, 24, 64, 30, 11, 128, 30 and 23 conditions (H1 ... CE, worked out by hand); a model of
  the control passes all twelve group checks, and one-entry changes break exactly the group
  stated.
- m107a check: the four names rebuild, all t2 with d = 2 and k <= 4, all in m106a's list.
- m107b, m107c check: 88 distinct cases, 58 + 7 + 23 by class, 56 + 21 + 11 by k, all d = 3, 44
  in this shard.
- m107e, m107f check: 6 and 4 items; with all groups, the clause hash, clause count and variable
  count equal m102's relax CNF for two items (e) and one (f); the group counts are the hand counts.
- Every job: no ERROR; every SAT verified outside the encoder. m107b, m107c: the control SAT at
  "none", verified. m107e, m107f: the control SAT with all groups, verified; every item ran; every
  item UNSAT with all twelve groups (the "none" CNF of m106e, UNSAT for each of them).

## Exploratory

- m107a: at least one of the four UNSAT at 900 s: about 45%. All four: about 20%.
- m107b + m107c: at least 44 of the 88 UNSAT at "none" or "n": about 50%. All 88 decided (UNSAT):
  about 20%. At least one SAT at "none": about 60%. Some case SAT at both "none" and "n": about
  25%. The k = 6 cases do better than the k = 10 cases (higher share UNSAT): about 70%. Nothing
  skipped for time: about 70%.
- m107e + m107f: M kept in every item: about 85%. Z kept in every item: about 55%. X and XE
  dropped in every item: about 60%. C kept in at least one item: about 50%. H2 kept in every item:
  about 45%. S1 kept in every item: about 45%. Every kept set has at most 5 of the 12 groups: about
  50%. The six core cases all keep the same set: about 25%. Every kept group proven needed (SAT on
  removal, not UNKNOWN): about 55%.
- Peak memory at most 1 GB in every job: about 90%. Each finishes within its timeout: about 80%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V** (any job): that would be a system with t = 8 and
  dim V = 11 (A(8) = 11). Re-check it by brute force in a separate job before saying anything.
- **m107a, all four UNSAT:** all 1,115 d = 2 cases with k <= 4 are UNSAT (uncertified): DRAT
  certificates next (job m108), each from the smallest CNF that was UNSAT for its case, at most four
  shards per run; all certified gives Proposition 39. Any still open: report it; certify the ten
  d = 2 classes that are complete.
- **m107b + m107c, all 88 UNSAT:** every t2 and t3 case of the three d = 3 classes is refuted
  (with the 57 certified k <= 4 cases); only t1 is left there. Then certificates of these 88 from
  the smaller CNF, and "none" on the k > 4 cases of the d = 2 classes, in shards of at most 3 hours.
  Many UNKNOWN: report by k and do not scale up. SAT at both levels: record the model; it shows
  what any refutation of that case must use beyond N.
- **m107e + m107f, a small kept set (at most 5 groups) shared by the core cases:** that is the
  target of a hand proof (Lemma 110): those conditions, the system (*) and the normal form are
  contradictory for that T(N). Write the lemma only if fully proved. Kept sets that differ by type:
  report them by type and attempt the simplest type first.
