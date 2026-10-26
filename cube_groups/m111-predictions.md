# Job m111: predictions, written 2026-10-26 in the run that started at 08:31Z, before the jobs ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m110a-g came back (notes/a103.md): of their 2,715 d = 1 cases with k(T(N)) <= 4, 2,389 were
UNSAT with anisotropy on N (60 s), 11 more with the full sweep CNF (120 s), and 315 stayed open.
Every graded check held. Shards h and i were stopped from outside at 08:22 UTC and are re-filed
unchanged; shard j had not come back.

**Already seen, not a prediction.** Read off the names, 313 of the 315 open cases have basis
matrices whose entries (2, 0) and (2, 1) are zero, so T(N) leaves span(q_0, q_1) = pi(R) invariant;
the two others are o008_c003 t2_m092 and o010_c003 t2_m092. Eight cases of that form were UNSAT at
"n" (o007_c001 t2_m026, o007_c005 t3_m004_034, o010_c004 t2_m011, o007_c008 t2_m011 and
t3_m011_017, o007_c009 t3_m011_017, o009_c008 t2_m011 and t3_m011_017), and at least two more at
the sweep. Read the same way, 27 of the 28 d = 2 cases that job m105 left UNKNOWN leave pi(R) (a line
at d = 2) invariant; the exception is o005_c001 t3_m024_109. Part "struct" checks all of this by
machine, with no use of the names.

## m111a (struct): graded (each must hold)

- Unit tests pass (8 in test_m111).
- 68 classes; |pi(R)| = 2^(3 - d) and |ker S| = 2^d in every class; Im S = pi(R) in every class;
  pi(R) = span(q_0, q_1) in all 34 d = 1 classes.
- 3,876 d = 1 cases; the row-2 rule equals "T(N) leaves pi(R) invariant" in every one.
- The seven m110 grade files load, 2,715 cases, every name among the 3,876.
- 1,078 d = 2 cases of m105 and the 28 UNKNOWN ones rebuilt.

## m111a: exploratory

- The struct counts match the reading above exactly (313 of 315 open; the 28 give 27): about 85%.
- T(N) leaves pi(R) invariant in 420 to 500 of all 3,876 d = 1 cases: about 65%.
- At d = 2, at most 30% of the 1,078 cases leave pi(R) invariant: about 60%.
- Leaving ker S (a line at d = 1) invariant goes with "open" much less: under half of the cases
  that leave ker S invariant are open: about 60%.
- T(N) commutes with S in most open cases: about 30%.
- The classes with Kbar of order 1 (179 cases each) have a lower UNSAT share than the others
  (carried over from m110-predictions.md): about 40%.

## m111b, m111c (levels): graded (each must hold)

- Unit tests pass (8).
- Check: the grade files load; one sample case per label of the open cases, each a d = 1 case that
  m110 left open; the sample is not empty; the control rebuilt under its name; the vector sets have 15 ("n"), 255 ("in4") and 127
  ("out3") vectors for every sample case and the control.
- The control o000_c000 t2_m511 is SAT at "n" with a verified model.
- No ERROR; every SAT model verified outside the encoder; every sample case ran (or was skipped
  for time) at "in4" and "out3"; the sweep CNF ran (or was skipped) exactly on the cases with no
  UNSAT level; no case is SAT at the sweep and UNSAT at a level.

## m111b, m111c: exploratory

- 22 to 26 labels in the sample (b and c together): about 70%.
- "in4" UNSAT for at least half the sample: about 40%. "out3": about 35%.
- At least one sample case decided at some level (either level or the 600 s sweep): about 75%.
  Every sample case decided: about 20%.
- The control SAT at "in4": about 40%; at "out3": about 40%.
- A verified model at "in4" or "out3" for some sample case: about 35%.
- A verified model anisotropic on all of V: about 1%.
- Nothing skipped: about 70%. Peak memory at most 1 GB: about 85%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11. Re-check it by
  brute force in a separate job before saying anything.
- **Struct confirms the reading:** write it as an observation (computer-checked count, not a
  theorem) and look for a hand reason: when T(N) leaves pi(R) invariant, every A_n (n in N) maps
  R + X_1 into A_u(R), of dimension 3 - d.
- **"in4" or "out3" decides at least 80% of the sample:** that level on every open d = 1 case
  (job m112), then DRAT certificates for all 3,876 (as m108), then Proposition 40.
- **Neither level decides half, the 600 s sweep decides most:** the sweep at 600 s on the open
  cases that leave pi(R) invariant, split by label.
- **Nothing decides:** the cases that leave pi(R) invariant need a finer split (by the action of
  T(N) on pi(R) and on Q / pi(R)) or a hand lemma; no blind escalation.
