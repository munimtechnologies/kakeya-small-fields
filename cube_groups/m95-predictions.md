# Job m95: predictions, written 2026-10-23 in the run that started at 21:33Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m94's pilot came back (notes/a87.md): type (N4) with W in m93's orbit of 10080 spaces at
(t, dim V) = (8, 11) was UNSAT in 2.57 s (0.62 s of solving; 142832 variables, 905882 clauses), and
all 9 graded checks held. By m94's rule ("UNSAT within 10 minutes"), the other orbits of (N4)
follow, and then the types with d = 3. Job m95 (cube_groups/m95.py) does both, in two groups.

**Group a (job m95a):** the 23 orbits that meet n4 (m93's orbit list, recomputed in the job with
m93.py), each with m94's CNF (m94.encode_n4, unchanged) for the basis m93 recorded. Each is solved
by python-sat with a 600 s cap and, if UNSAT, certified: a standalone CaDiCaL (rel-2.2.1) writes a
DRAT proof and drat-trim checks it (cert1.py's tools, unchanged). Then a ladder on the pilot's CNF:

    relax_t6    m94's (6, 3) control without its 2^8 - 1 anisotropy clauses
    relax       the pilot without its 2^11 - 1 anisotropy clauses
    drop_units  the pilot without the 16 units of (N4)
    drop_inv    without the 15 one-to-one clauses
    drop_lin    without the 96 conditions (S)
    drop_a      without the 84 units (a)
    drop_lin_a  without (S) and (a): the matrices M_n left free, the whole of (N4) in one CNF

(caps: 600 s for the two relax runs, 300 s for the others). A model of a relax run must be a
system (*) in the normal form of shape (c) with all four families of new conditions, checked by
brute force, and must not be anisotropic. The relax runs are the positive controls that m94 lacked:
they show whether the new clauses are consistent with the system equations, so that the UNSAT
answers depend on anisotropy.

**Group b (job m95b):** d = 3, types (N3) and (F3) together. For each of the 73 orbits with an
invariant hyperplane and each hyperplane D = ker f invariant under the recorded basis, the CNF is
m94's with the 16 units of (N4) replaced by

    (D)   rows 4 to 7 of A_u applied to each of the three basis vectors of D are 0 (12 equations),
    (O)   rows 4 to 7 of A_u e_(4 + l0) are not all 0, e_l0 a basis vector outside D (one clause),

and the 15 one-to-one clauses taken over all 8 rows (the columns of T need not lie in X_1). These
say that T(D) lies in X_1 and T(F_2^4) does not, that is D = T^(-1)(X_1 n R), which by Lemma 95(d)
is a W-invariant hyperplane; after Lemma 96 fixes the tuple, D is one of the invariant hyperplanes
of the fixed basis, so the instances cover every system of rank 4 with d = 3. Each is solved by
python-sat with a 120 s cap; no instance starts after 130 minutes (SKIPPED). No certificates yet.

If every instance of both groups is UNSAT, no element of rank 4 exists at (8, 11). That would rest
on Corollary 121 and Lemmas 38, 39, 94, 95 and 96 (hand arguments no human has checked), on m93's
orbit list, on the encoding, and on the solver answers. A(8) <= 10 would still need (B7)_8 and
(B6)_8 (Proposition 36).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

Both groups, from the selfcheck step:

1. m93_tables: m93's own table checks (|GL_4(F_2)|, ranks, inverses, 34 classes, orbit-stabiliser,
   Feit and Fine).
2. m93_dim3: the sweep of dimension 3 is complete, its orbit sizes add up to the double count, and
   every representative is valid.
3. orbits_all, orbits_n4, orbits_hyper: 79 orbits (160408 subspaces), 23 meeting n4 (47595), 73
   with an invariant hyperplane (153240), as m93 found.
4. hyper_counts: for every orbit, m95's list of invariant hyperplanes has m93's count.
5. hyper_invariant: every listed ker f is mapped into itself by each basis matrix, vector by
   vector.
6. pilot_in_n4: m94's basis (1, 64, 1056) is the recorded basis of an n4 orbit of size 10080.
7. encode_t8, encode_t6: m95's encoder with d = 4 gives m94.encode_n4's clauses exactly, and the
   variable, clause, start and first-variable counts that m94's job recorded.
8. aniso_t8, aniso_t6: the relax filter finds exactly 2^11 - 1 and 2^8 - 1 anisotropy clauses.

Group a only, the tool controls of cert1:

9. tools built; PHP(6, 5) UNSAT with its proof VERIFIED; an empty proof rejected; PHP(5, 5) SAT
   with a model that satisfies every clause.

So 12 graded checks in m95b and 16 in m95a, plus one for each SAT answer (its model verified by
brute force: (*) on all pairs, anisotropy, the normal form, every family the CNF kept; for a relax
run, not anisotropic).

## Exploratory, with the decision rules

Group a:

- **All 16 graded checks hold: about 85%.**
- **All 23 (N4) instances UNSAT within 600 s each: about 85%.** Any SAT: about 2%.
- **All 23 VERIFIED by drat-trim: about 82%.**
- **Every python-sat solve at most 60 s: about 75%.**
- **relax SAT with a verified, non-anisotropic model: about 65%; relax_t6 the same: about 70%.**
- **drop_lin_a UNSAT within 300 s: about 25%.** drop_a about 55%, drop_lin about 45%, drop_inv
  about 75%, drop_units about 45%.

Group b:

- **All 12 graded checks hold: about 88%.**
- **Between 150 and 450 instances: about 60%.**
- **Every instance reached (none SKIPPED): about 75%.**
- **All UNSAT: about 40%; at least 90% of them UNSAT: about 65%.** Any SAT: about 3%.
- **Median UNSAT solve at most 30 s: about 55%.**

Both: **peak memory at most 1.5 GB: about 80%.**

Rules:

- **Group a all UNSAT and relax SAT with a verified model:** type (N4) is closed for every orbit
  (computer-assisted; with DRAT proofs if all VERIFIED). Written up as Corollary 122.
- **relax UNSAT:** the refutation does not use anisotropy, which the hand lemmas do not predict. No
  claim: check (S) and (a) against Lemma 38(a) by hand and look for an encoding error first.
- **relax UNKNOWN:** no claim changes; say so, and re-run relax alone with a longer cap.
- **Group b all UNSAT:** d = 3 is closed, and with group a no element of rank 4 exists at (8, 11)
  (Proposition 37, computer-assisted). Next: certificates for group b, a relax control at d = 3
  (one that keeps the one-to-one clauses), then (B7)_8 and (B6)_8 by hand.
- **Group b some UNKNOWN or SKIPPED:** re-run exactly those with a 30-minute cap (job m96); if
  they stay open, split them by T.
- **Any SAT, verified:** no claim until a separate job re-checks the model by brute force; a true
  one would be an anisotropic system with t = 8 and dim V = 11, so A(8) = 11.
- **A graded check fails:** a bug; fix, re-run as -v2, count nothing.
