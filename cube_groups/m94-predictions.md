# Job m94: predictions, written 2026-10-23 in the run that started at 20:06Z, before its job file

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m93 counted the orbits of the space W = span{M_n : n in N_Y} of Lemma 95 (notes/a85.md, a86.md):
79 orbits of 3-dimensional commutative subspaces of M_4(F_2) without I, of which 23 meet the
condition of type (N4), 21 that of (F3) and 73 have an invariant hyperplane. By m93's decision rule
("a few hundred orbits or fewer"), the next step is the shape (c) search at (t, k) = (8, 4), adapted
from job m44 (Lemmas 85 and 86, notes/a35.md), with ONE pilot instance before any queue.

The pilot (cube_groups/m94.py) is the CNF of case_b_shapes.encode_shape(8, 4, 'c') (dim V = 11) with

    (N4)  Im A_u = ker A_u: rows 4 to 7 of A_u e_c are 0 for c >= 4 (16 unit clauses), and
          T = A_u on [e_4], ..., [e_7] is one-to-one (15 clauses: no non-empty set of its columns
          adds up to 0); T itself is left free (16 variables);
    (M)   M_(v_1), M_(v_2), M_(v_3) fixed to E_00, E_12, E_11 + E_22, the basis job m93 recorded for
          its orbit of size 10080 (mask 1, 64, 1056; singular, common kernel of dimension 1, sum of
          images of dimension 3, meets (N4) and (F3)), the largest orbit that meets (N4);
    (S)   A_(v_i) e_(4+j) = A_u (sum over l of M_i[l][j] e_(4+l)): 3 x 4 x 8 = 96 linear conditions;
    (a)   rows 4 to 7 of beta(v_i, v_(3+j)) are 0 for j = 1, 2, 3 and column j - 4 of M_i for
          j >= 4: 3 x 7 x 4 = 84 unit clauses.

Why fixing all three matrices is allowed: by Lemma 95(b) (Lemma 39 with k = 4) the system has a
normal form of shape (c) for every conjugate g^(-1) W g, and the recombination in GL_3(F_2) turns any
basis of the space into any other, so the tuple can be taken to be the recorded basis; the type of
A_u is kept by every base change. So a system of type (N4) whose W lies in this orbit gives a model
of this CNF. An UNSAT answer closes (N4) for this one orbit only; it rests on Lemma 95 and Lemma 39
(hand arguments no human has checked) and on m93's orbit list.

Controls: case_b's (t, k) = (2, 1) example SAT with a verified model; the same encoder at
(t, k) = (6, 3) with M_(v_1), M_(v_2) = N, N^2 (N the 3 x 3 shift) and A_u of type (N4) must be
UNSAT, since A(6) = 6 (Theorem 31) and dim V = 8. There is no positive control in shape (c): a
satisfiable instance at t <= 7 with dim V = t + k - 1 would contradict A(t) = t or A(7) <= 8. The
unit tests check the new clauses on hand-made data instead (they hold for data built from (S) and
(a), and fail for a wrong A_(v_1), a singular T, an image outside ker A_u, and a wrong beta).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. case_b and case_b_shapes: their own selfchecks.
2. w_space: the three masks are independent, commute, and I is not in their span.
3. w_orbit: the orbit of their span under GL_4(F_2) has 10080 elements.
4. w_flags: m93's flags for it: singular, n4 and f3 true, common kernel 1, sum of images 3.
5. hints_t8, hints_t6: the counts 96, 84, 16, 15 at (8, 4) and 36, 30, 9, 7 at (6, 3), with unit
   clauses that do not contradict each other.
6. cb_t2_k1: SAT with a verified model.
7. n4_t6_k3: UNSAT.
8. If the pilot is SAT: its model verified by brute force (is_system and anisotropic on all
   2^11 x 2^11 pairs, the normal form of shape (c), and (N4), (M), (S), (a) read back).

So 9 graded checks (10 if the pilot is SAT).

## Exploratory, with the decision rules

- **All 9 graded checks hold: about 85%.**
- **The pilot's CNF has 100,000 to 250,000 variables: about 70%; 0.7 to 1.5 million clauses: about
  70%.** (Job m83's CNFs at (7, 9) had 48,587 variables and 286,239 clauses.)
- **The pilot is UNSAT within its 75-minute cap: about 35%.** Within 10 minutes: about 15%.
- **The pilot is SAT: about 2%.** (A verified model would be an anisotropic system with t = 8 and
  dim V = 11, so A(8) = 11; it would be checked again by an independent brute force before any
  claim.)
- **The control at (6, 3) is UNSAT within 60 seconds: about 80%.**
- **Peak memory at most 1.5 GB: about 85%.**

Rules:

- **UNSAT within 10 minutes:** queue the other 22 orbits of (N4) the same way (one job, two
  groups), then design (F3) and (N3), which also fix the invariant hyperplane D of Lemma 95(d).
- **UNSAT in 10 to 75 minutes:** before a queue, split further: T up to the normaliser of W, or
  extra necessary conditions from Lemma 94(c); pilot again.
- **UNKNOWN:** this route costs too much at this granularity. Hand work first (route (1) of
  a84.md: Lemma 94(c) for the singular M_n), and a second pilot only with T fixed as well.
- **SAT, verified:** no claim until an independent re-check (the model put through sat_aniso.py's
  brute force in a separate job) agrees.
- **A graded check fails:** a bug; fix, re-run as -v2, count nothing.
