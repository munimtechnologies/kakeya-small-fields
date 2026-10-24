# Job m97: predictions, written 2026-10-24 in the run that started at 01:05Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m96 came back (notes/a89.md). Without anisotropy ("relax"), the CNF of type (N4) has checked
models at (4, 2) for M = N and E, and at (6, 3) for (E_00, E_11) and (E_00, E_12). It has none for
I + N, F, (N, N^2), m94's pilot at (8, 4) or the pilot with d = 3, f = 1. a89.md proves by hand
**Lemma 98**: in type (N4), without anisotropy, M_y^2 = M_(n(z_y)) with z_y = G_y y, and
(G_y + G_y^2) y = 0. **Lemma 99** draws three consequences: M^2 is 0 or M at k = 2 (exactly m96's
split at t = 4), (N, N^2) has no system at (6, 3), and with anisotropy no M_y is idempotent. The
last one rules out by hand the 8 orbits at (8, 4) whose basis starts with E_00, the pilot among
them.

Job m97 (cube_groups/m97.py) tests this. It reads Lemma 98 off every model the solver finds, and it
solves a small "reduced system" built only from Lemma 98 and (5) for the 7 small instances and the
23 orbits of type (N4) at (8, 4). The levels are relax, aniso1 (q(y) != 0) and aniso2 (also
dim span q(Y) >= k - 1, Lemma 38(e)). It also solves the relax CNF of all 23 orbits at (8, 4),
the positive control that m95 did not have.

## Graded (each must hold; a failure means a bug in Lemma 98 or in the code: find it, count nothing)

- Unit tests pass (step 1). They include the hand results: the reduced system is SAT for N and E
  and UNSAT for I + N and F (stage "linear"), UNSAT for (N, N^2) (no invertible S, from one choice
  of G), and aniso1 is UNSAT for the 8 orbits whose basis starts with E_00.
- selfcheck: the 23 orbits of type (N4) in m95's published m95_orbits.json equal N4_ORBITS, the
  pilot is orbit 5 (size 10080), and every tuple passes m94.check_tuple.
- reduced, relax level: SAT for t4_N, t4_E, t6_e00e11, t6_e00e12 and UNSAT for t4_IN, t4_F,
  t6_shift.
- models (t <= 6): the relax answer equals m96a's for all 7 instances (another encoder path,
  m95.encode_rank4 + m95.relax); each relax drops exactly 2^d - 1 clauses; every model found passes
  (*) as (L) and (Q) and by brute force, the normal form and shape (c), each family of m95, every
  identity of Lemmas 98 and 46(a) and (5), and is not anisotropic; a SAT instance has a SAT reduced
  system.
- t8: each relax drops 2047 clauses; every model passes the same checks ((*) as (L) and (Q) only);
  an orbit with a relax model has a SAT reduced system; the pilot's relax is UNSAT (as in m95 and
  m96).

Counted in "graded N": 4 + 1 + 7 + 1 + 7 + 7 + 4 + 4 + 23 + 1 = 59, plus 2 for each orbit at
(8, 4) with a relax model.

## Exploratory

- **reduced aniso1 UNSAT for at least the 8 orbits with E_00: about 97%.**
- **reduced aniso2 UNSAT for all 23 orbits: about 20%.** For at least 12 of 23: about 50%.
- **reduced relax UNSAT at the pilot: about 35%.**
- **t8 relax SAT for at least one orbit: about 55%.**
- **For every orbit with a decided relax answer, reduced relax and relax agree: about 40%.**
- **Some reduced answer UNKNOWN (cap on the search for an invertible S): about 10%.**
- **Every t8 relax decided within 90 s: about 85%.**
- **Peak memory at most 1.5 GB: about 85%.**

## Decision rules

- **A graded identity fails on a model:** Lemma 98, Lemma 99 or the code that reads the model is
  wrong. Find which before anything else; no part of a89.md is used until then.
- **All graded checks hold and reduced aniso2 is UNSAT for all 23 orbits:** type (N4) at (8, 11)
  is closed by hand lemmas plus a small enumeration (at most 4096 choices of G and linear algebra
  over F_2 per orbit), independently of m95a's large CNFs. Next run writes this up as Proposition 37
  for (N4) (computer-assisted, small), with m95a's 23 certified UNSAT answers as a second check.
  Then d = 3 (m95b) needs a version of Lemma 98 with L != 0.
- **Some orbits survive aniso2, and t8 relax has a model that passes every check for some orbit:**
  the encoder has a positive control at t = 8. m95a's answers then count for the surviving orbits
  (computer-assisted, certified), with the failed control of m95 and its explanation (a89.md)
  stated.
- **Some orbits survive aniso2 and t8 relax is UNSAT for all 23:** still no control at t = 8. Next:
  a hand reason for the pilot's relax refutation (Lemma 98 applied to elements outside W), or a
  control that changes the type rather than dropping anisotropy.
