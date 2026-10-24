# Job m101: predictions, written 2026-10-24 in the run that started at 12:12Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m100 came back (notes/a93.md). Every graded check held (14 of 14 in each half), and all four
positive controls without anisotropy were SAT in about 2 s with verified models. But all 68 rank-0
sweeps were UNKNOWN at 180 s. Its decision rule for fewer than 5 UNSAT: hand work on the rank-0
case, and no larger sweep budget without a new reason. a93.md does the hand work and finds a new
reason. **Lemma 104:** in the rank-0 case the maps of N = ker phi are A_u T_n with commuting T_n in
End(X / X_1), so some w != 0 in N has A_w = 0. **Lemma 105** (Lemma 89 at t = 8):
C = beta(w, V) + span(sigma(w)) lies in X_1, its dimension 3 is ruled out by M(5) = 5, and unless
A_u is idempotent, x0 is not in C.

Job m101 (cube_groups/m101.py, two jobs as m100: m101a for pair orbits 0 to 8, 31 classes; m101b
for pair orbits 9 to 12, 37 classes). For each class of (B7)_8 it runs m100's sweep instance
(unchanged, as a prefix) plus A_(v_1) = 0 (64 units), beta(v_1, e_j) in X_1 (30 units, implied), and,
in the 66 classes where A_u is not idempotent, "x0 not in C" through a functional f on X_1
(11 generators). The cap is 180 s each, CNF build included. Before that, two classes per half are
run twice as positive controls, at 90 s each: "relax" has no anisotropy clauses, and "relax_n" keeps
anisotropy only on N (15 clauses). relax_n rules out the trivial model with sigma = 0 on N.

## Graded (each must hold)

- Unit tests pass (6).
- check, in each half (10 checks): 68 classes; X_1 = span(e_0, ..., e_4) in all 13 pair orbits;
  the idempotent classes found by machine are exactly o011_c005 and o012_c010 (found by hand), both
  with d = 0 and class size 1; x0 = e_0; v_1, v_2, v_3 in ker phi; m100's sweep CNF is an unchanged
  prefix (SHA-256 over its clauses); 64 + 30 + 11 added conditions and 144 sweep conditions in every
  mode; 2047 anisotropy clauses in the sweep CNF, none in relax, 15 in relax_n; the halves cover
  the 13 pair orbits.
- grade, in each half: every class of the half has a sweep row, and there is no ERROR. Every SAT
  answer passes its check outside the encoder: (*) on all 2^11 x 2^11 pairs, the normal form, the
  sweep conditions, A_(v_1) = 0, C in X_1, x0 not in C (where required), anisotropy (sweep) or
  anisotropy on N (relax_n).

## Exploratory

- **Controls: all four relax SAT: about 95%.** (A model of m100's control with zero on v_1 to v_3
  satisfies every added condition, so only the solver's time is in question.) **At least one of the
  four relax_n SAT: about 60%**, all four decided within 90 s: about 50%.
- **Any sweep SAT: about 1%.**
- **At least one of the 68 sweeps UNSAT: about 45%.** At least 20 UNSAT: about 15%. All 68 UNSAT:
  about 5%.
- If any are UNSAT, they are mostly in d = 0 or 1, not d >= 2: about 65%.
- The two idempotent classes (no case-two clauses) are UNKNOWN: about 70%.
- Peak memory at most 2 GB in both: about 90%. Both finish within 150 minutes: about 85%.

## Decision rules

- **A check fails:** nothing in that half counts until it is explained.
- **A sweep SAT answer that passes every check:** an anisotropic system with t = 8 and dim V = 11,
  so A(8) = 11. Before saying so, re-check it by brute force in a separate job and against Lemmas
  102 to 105.
- **A sweep UNSAT:** in that class, every system has an element of N whose map is not zero on X_1
  (the rank-0 case is closed there, given Lemmas 104 and 105). A sweep alone closes no class.
- **All 68 UNSAT:** the rank-0 case of (B7)_8 is closed. Next: certify them with DRAT proofs, then
  turn to rank >= 1 on X_1 (Lemma 103 (a)).
- **Fewer than 5 UNSAT:** zero maps alone do not make the rank-0 case decidable at this budget.
  Next is the case split on the commuting space T(N) (Lemma 104): fix A_(v_2), A_(v_3) by their
  classes, which fixes every A_n with n in N, before any larger budget.
- **A relax control UNSAT:** the added conditions contradict the base instance without
  anisotropy, which Lemma 105 does not predict. Find the error before anything counts.
- **All four relax_n UNKNOWN or UNSAT:** UNSAT answers still count (a relaxed CNF that is UNSAT
  makes the full one UNSAT), but they do not show what closes them.
