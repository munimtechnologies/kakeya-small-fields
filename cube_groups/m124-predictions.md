# Job m124 (pilot): predictions (written 2026-10-28 ~17:30 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

30 of the 3,876 d = 1 cases with k(T(N)) <= 4 have no UNSAT answer (notes/a109.md to a111.md). The
pilot m121 split four cases on K = 3 entries of A_(h_1) into 8 cubes at 600 s; two of its cases
turned out to be among m111b's refutations, and on the two that are open, 1 and 2 of 8 cubes stayed
UNKNOWN, all with the first entry false. By m121's decision rule m124 splits further, adaptively: a
node (a sign pattern of the first d variables in m124's order) is solved by CaDiCaL at 90 s, and if
UNKNOWN it is split on the next variable, down to depth 10, where the cap is 1,200 s. Each case gets
at most 40 minutes, two nodes at a time. No proofs yet.

## Graded (each must hold)

- Unit tests (7 in test_m124).
- Check: 30 open cases (3,876 less 3,408, 423 and 15); four pilot cases, one per label of m121
  (t2 m011, t2 m026, t2 m031, t3 m011_017), none among m111b-c's refutations; the UNSAT control is
  one of m111b's.
- SAT control (o007_c008 t2_m012, "n" CNF, first 3 levels forced): 7 forced nodes, verdict SAT,
  every SAT model satisfies the CNF.
- UNSAT control (o007_c001 t3_m011_017, sweep CNF): verdict UNSAT with a complete tree, within 40
  minutes.
- Every pilot case accounted for; every tree complete (leaf weights sum to 1); no ERROR; every SAT
  model satisfies the CNF.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds: 55% (the UNSAT control may not finish in 40 minutes).
2. At least one of the four pilot cases UNSAT: 40%.
3. At least one of m121's two open cases (o007_c003 t2_m026, o007_c007 t2_m031) UNSAT: 30%.
4. All four UNSAT: 10%.
5. A SAT leaf on a pilot case: 3%.
6. In every pilot tree, every open leaf has the first variable false: 80%.
7. Peak memory under 2 GB: 90%.

## Decision rules

- **A pilot case UNSAT:** the adaptive split works for its label. Next: the same on all 30 open
  cases (about 40 minutes each, in shards), then DRAT proofs per leaf for the UNSAT ones.
- **All OPEN, with the open leaves deep on one branch:** the hardness is not in the variables split
  on. Read the open leaves (which entries are false) and look for a hand lemma for that branch, or
  split on T(N) acting on Q/pi(R) instead.
- **All OPEN, open leaves spread over many branches:** splitting does not cut the work; stop the
  cube route on these cases and record them as open.
- **A SAT leaf:** stop and read the model back (it satisfies the CNF, m100's checks, anisotropy on
  all of V); a verified model would be a system with t = 8 and dim V = 11, to be re-checked by brute
  force in a separate job before anything is said.

An UNSAT answer here is a solver answer without a certificate until a per-leaf DRAT run. No human
mathematician has checked any of it.
