# Job m100: predictions, written 2026-10-24 in the run that started at 08:34Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m99 came back (notes/a92.md): all 24 graded checks held. (B7)_8 has 13 pair orbits and 68
classes of A_u, (B6)_8 has 51 and 422, and the six pilot instances (whole classes, no split) were
UNKNOWN at 240 s each. Its decision rule for that case: hand work first. a92.md does it: Lemma 102
(Lemma 88 at t = 8) and Lemma 103 (Lemma 93 at t = 8).

Job m100 (cube_groups/m100.py, two jobs: m100a for pair orbits 0 to 8, 31 classes; m100b for pair
orbits 9 to 12, 37 classes) runs the rank-0 sweep of Lemma 103 for every class of (B7)_8: m42's
instance (unchanged, downloaded from the repository) plus A_(v_i) X_1 = 0 and beta(v_i, v_j) = 0
for 1 <= i < j <= 3 (144 conditions), 180 s each (CNF build included). Before that, two classes per
shard are run with the anisotropy clauses switched off (90 s each), as a positive control.

## Graded (each must hold)

- Unit tests pass (8).
- check, in each shard (10 each): 68 classes; per-pair counts as m99 (1, 1, 1, 5, 2, 4, 2, 10, 5,
  10, 9, 6, 12); class sizes add up to 168 per pair; d per pair as m99 (3, 3, 3, 2, 2, 2, 2, 1, 1, 1,
  1, 0, 0); every representative has rank 3, kernel span(x1) and image span(r); the shards cover
  the 13 pairs; m100.encode_fixed gives the same clauses as m42.encode_fixed on a real (8, 11)
  instance (SHA-256 over the clause list); that CNF has exactly 2047 anisotropy clauses; the relax
  CNF has none; the sweep adds 144 conditions.
- grade, in each shard: every class of the shard has a sweep row; no ERROR; every SAT answer passes
  its check outside the encoder ((*) by sat_aniso.is_system on all 2^11 x 2^11 pairs, the normal
  form, the sweep conditions, and for sweep answers also anisotropy).

## Exploratory

- **Control: at least one of the four relax instances SAT: about 55%.** All four decided within
  90 s: about 60%. (At (8, 11) with rank 4, 14 of 159 relax CNFs were SAT; here N has three free
  elements and the system has more room, but A_u's data is fixed.)
- **Any sweep SAT: about 1%.**
- **At least one of the 68 sweeps UNSAT: about 65%.** (At t = 7, m64a closed 21 of 51 sweeps of
  (B6) at 150 s: all 7 with d = 0, 10 of 27 with d = 1, none of 13 with d = 2. At t = 8, N has one
  more free element and V two more dimensions.)
- **At least 9 of the 18 classes with d = 0 UNSAT: about 35%.**
- **No class with d >= 2 UNSAT: about 80%.**
- Between 5 and 30 UNSAT in all: about 40%.
- Peak memory at most 2 GB in both: about 90%. Both finish within 150 minutes: about 85%.

## Decision rules

- **A check fails:** nothing in that shard counts until it is explained (a wrong representative
  or a different m42 on GitHub would show here).
- **A sweep SAT answer that passes every check:** an anisotropic system with t = 8 and dim V = 11
  exists, so A(8) = 11. Before saying so, re-check it by brute force in a separate job and against
  every lemma it would contradict.
- **A sweep UNSAT:** every system of that class has an element of N whose map is not zero on X_1.
  By Lemma 103 (a) its second-matrix split needs only the representatives of rank >= 1 on X_1. A
  sweep alone closes no class.
- **20 or more sweeps UNSAT:** the sweep is a lever at t = 8; the next job counts the classes of
  the second matrix (Proposition 38, the analogue of Proposition 33) by machine for the classes
  with d = 0, and the next note counts them by hand first.
- **Fewer than 5 UNSAT:** the rank-0 case is hard at t = 8. Next is hand work on it (Lemma 103 (b):
  sigma is linear and one-to-one on N, beta vanishes on N x N), and no larger sweep budget is
  queued without a new reason.
- **All four controls UNSAT:** the sweep's UNSAT answers still count (a relaxed CNF that is UNSAT
  makes the full one UNSAT), but they do not show that anisotropy is what closes them; the next
  job then looks for a positive control elsewhere (for example the planted system of m42 at t = 6).
