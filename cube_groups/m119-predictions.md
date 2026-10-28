# Job m119: predictions (written 2026-10-28 ~01:40 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Of the 3,876 d = 1 cases with k(T(N)) <= 4, 3,845 have UNSAT answers and 30 stayed UNKNOWN at
1,500 s (notes/a108.md). One case, o010_c008 t3_m012_032, has never been run at 1,500 s: shard
m112l skipped it when its time ran out. Job m119 runs it, with m110's controls.

## Graded (each must hold)

- Unit tests (3 in test_m119).
- Check: m112l's grade file lists the case as skipped and not UNSAT; it is a d = 1 case.
- Controls: m110's three controls SAT at "n", each model verified outside the encoder.
- No ERROR; a SAT model is verified; the case is accounted for.

## Exploratory

- UNSAT within 1,500 s: about 75% (the label t3 m012_032 has not stayed UNKNOWN anywhere; 93.6%
  of the cases m112 ran were UNSAT).
- If UNSAT, wall time above 600 s: about 65%.
- A SAT answer: about 2%.

## Decision rules

- **UNSAT:** 3,846 of 3,876; the case joins the sweep-certificate run sized from m117.
- **UNKNOWN:** it joins the cube-and-conquer list with the other 30.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11; re-check it by
  brute force in a separate job before saying anything.
