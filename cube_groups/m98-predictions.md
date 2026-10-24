# Job m98: predictions, written 2026-10-24 in the run that started at 03:05Z, before the jobs ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m97 came back (notes/a90.md): 67 of 69 graded checks held, and every identity of Lemma 98 held
on every model it read at t = 4, 6 and 8. Without anisotropy the CNF of type (N4) at (8, 4) has
checked models for orbits 0, 1, 6, 14 and 29, so the encoder has a positive control at t = 8. With
anisotropy the reduced system is UNSAT for 20 of the 23 orbits and SAT for orbits 18, 29 and 40.
The two failed checks: orbits 0 and 14 have relax models, but the reduced system answered UNKNOWN,
because m97.invertible_in only tried combinations of the first 12 basis vectors of a solution
space. Two things are still unchecked: that the pair (G, S = T^(-1)) of every model really lies in
the space m97.reduced searches (the 6 orbits ruled out by "no invertible S" rest on that), and
whether d = 3 has a positive control.

Job m98a (cube_groups/m98.py) checks both and decides the reduced system without a cap. Job m98b
certifies m95b's 159 answers for d = 3 with DRAT proofs.

## Graded, job m98a (each must hold)

- Unit tests pass.
- selfcheck: m97's 23 orbits equal m95_orbits.json's; there are 159 instances with d = 3, the pilot
  with f = 1 among them; at d = 4, relax by prefix gives exactly m95.relax's clauses (2047 dropped);
  at d = 3 (pilot, f = 1) relax by prefix drops exactly 2047 clauses. (6 checks)
- consistent: for each of t4_N, t4_E, t6_e00e11, t6_e00e12 (6 models each) and orbits 0, 1, 6, 14,
  29 (3 models each): relax SAT; every model passes every identity of m97; and the pair (G, S) read
  off every model has G_a x0 = e_a, G_a e_a = z_(e_a), G_a e_b + G_b e_a as m97.reduced fixes it,
  z_y = G_y y, G_y z_y = z_y, S invertible, M_i S w_y = S H_y e_i for every y and i (recomputed
  by matrix products), q(y) = S w_y, G_y keeps X_1 and T maps into X_1. (27 checks)
- reduced2: all 30 instances at all 3 levels decided (no UNKNOWN), equal to m97's answer wherever
  m97 decided, and SAT for orbits 0 and 14 without anisotropy (their relax models force it).
  Every SAT witness passes the same recomputed check. (90 + one per SAT answer, 20 expected)
- d3: all 159 instances run; each relax by prefix drops 2047 clauses; every relax model passes (L)
  and (Q), shape (c), every family of m95 with D = ker f, and is not anisotropic.

## Graded, job m98b

- Unit tests pass; cert1's three tool controls pass (PHP(6, 5) VERIFIED, the empty proof rejected,
  PHP(5, 5) SAT with a checked model).
- All 159 instances of m95b come back UNSAT with a DRAT proof VERIFIED by drat-trim. (160 checks)

## Exploratory

- **d3 relax SAT for at least one of the 159 instances (a positive control for d = 3): about 70%.**
  For at least 40: about 35%. The pilot with f = 1 stays UNSAT (as in m96b): about 97%.
- **Every d3 relax decided within 60 s: about 90%.**
- **Lemma 98(a) as stated (M_y^2 = M_(n(z_y))) holds on every d3 model: about 30%** (L != 0 adds
  error terms). G_y keeps X_1 on every d3 model: about 75%.
- **reduced2 takes at most 10 minutes in all: about 85%.**
- **The witnesses for orbits 0 and 14 pass aniso1: about 5%** (m97 found aniso1 UNSAT for both).
- **m98b: all 159 VERIFIED: about 92%; within 60 minutes: about 80%.**
- **Peak memory at most 2 GB in both jobs: about 85%.**

## Decision rules

- **A consistent or witness check fails:** the reduced system is not sound as built (most likely
  G_a x0 = e_a, or the pair conditions). The 6 orbits it rules out (20, 21, 30, 35, 39, 41) then rest
  on m95a's certified CNFs only. Find the cause before anything else.
- **All of m98a holds:** type (N4) at (8, 11) is closed (next run writes Proposition 37,
  computer-assisted): 14 orbits by hand (Lemma 100), 6 by the reduced system (a complete search of
  at most 4096 choices of G each, checked against 39 solver models), and orbits 18, 29 and 40 by
  m95a's DRAT-certified CNFs, which now have a positive control at t = 8.
- **d3 relax SAT somewhere and m98b all VERIFIED:** the d = 3 half (types (N3) and (F3)) is closed
  as well, computer-assisted. Then "no element of rank 4 at (8, 11)" (Corollary 121's open case)
  holds; A(8) <= 10 still needs Proposition 36's other configurations, (B7)_8 and (B6)_8.
- **d3 relax UNSAT for all 159:** no control for d = 3. Next: a reason by hand, as Lemma 98 was
  for d = 4 (Lemma 98 with L != 0), before m95b's answers count.
