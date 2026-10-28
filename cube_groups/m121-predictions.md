# Job m121 (pilot): predictions (written 2026-10-28 ~03:00 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

30 of the 3,876 d = 1 cases with k(T(N)) <= 4 stayed UNKNOWN at 1,500 s with m102's sweep CNF
(notes/a108.md, a109.md). The decision rules say: split, do not raise the cap. m121 splits one case
of each of the four most common open labels (t2 m011, t2 m026, t2 m031, t3 m011_017; 24 of the 30)
on K = 3 free entries of A_(h_1), the ones in most clauses, into 8 cubes that together cover every
assignment, and solves each cube with the CaDiCaL binary at 600 s, two at a time. No proofs yet.

## Graded (each must hold)

- Unit tests (4 in test_m121).
- Check: 30 open cases (3,876 less 3,408 less 438); four pilot cases, one per label.
- Control: the same split of the "n" CNF of the SAT control o007_c008 t2_m012 gives 8 cubes on 3
  variables, at least one SAT, every SAT model satisfying the CNF.
- Every pilot case accounted for, with 8 cubes on 3 variables; no ERROR; every SAT model satisfies
  the CNF.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds: 70%.
2. At least one of the four cases is UNSAT in all 8 cubes: 45%.
3. All four cases UNSAT in all cubes: 15%.
4. At least half of all 32 cubes are UNSAT within 600 s: 50%.
5. A SAT cube on a pilot case: 3%.
6. Every cube that is UNSAT takes under 300 s: 40%.

## Decision rules

- **A case UNSAT in every cube:** the split works for its label. File cube and conquer with DRAT
  proofs per cube for all 30 open cases (K = 3, or K = 4 for labels where some cube took over
  300 s).
- **Cubes UNKNOWN at 600 s:** splitting on A_(h_1) entries does not cut the work enough. Next pilot:
  K = 5 on the same entries, or split on T(N) acting on Q/pi(R) instead, on these four cases only.
- **A SAT cube:** stop and read the model back (it satisfies the CNF, m100's checks, anisotropy on
  all of V); a verified model would be a system with t = 8 and dim V = 11, to be re-checked by brute
  force in a separate job before anything is said.

The result stays computer-assisted, and an UNSAT answer here is a solver answer without a
certificate until the per-cube DRAT run. No human mathematician has checked any of it.
