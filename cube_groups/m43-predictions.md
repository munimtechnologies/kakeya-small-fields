# Job m43 (m43a to m43d): predictions, written 2026-10-19 ~21:00Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m43.py (Apache-2.0), with
sat_aniso.py, case_b.py and case_b_shapes.py from the repository. Setting: notes/a28.md, Lemma 84
(shape (d2) of Case B at rank 4 for t = 7 and dim V = 9, forms d2c0 and d2c1 of Lemma 37; the image
R = Im A_u up to K = {g : g e_0 = e_0, g e_1 = e_1, g e_2 = e_2, g P = P}, then A_u up to the
stabiliser of R).

## Graded (each must hold)

Validity checks (a failure means a bug: fix, re-run as -v2, count nothing from that job):
1. Unit tests pass; the selfchecks of case_b.py and case_b_shapes.py pass.
2. |K| by formula: 4, 96, 10752, 5160960 for t = 4, 5, 6, 7; at t = 4, 5, 6 also by enumeration.
3. Every transvection generator lies in K; every random unit lies in the stabiliser of its R.
4. The orbits of R (subspaces of dimension t - 3 containing delta) have sizes adding up to 1, 15,
   155, 1395 for t = 4, 5, 6, 7, each dividing |K|.
5. At t = 4, 5, 6: |Stab(R)| x (orbit size) = |K| for every representative, and the computed classes
   of A_u are exactly the orbits of the whole stabiliser.
6. At t = 7: in every orbit of R the class sizes add up to 20160, every member has kernel
   span(e_0, e_1, e_2) and image R, each class size divides |K| / (orbit size); every
   representative has rank 4.
7. Linear conditions: 33, 42, 51, 60 for t = 4, 5, 6, 7; unit clauses for A_u: 4, 10, 18, 28; no two
   unit clauses contradict.

Agreement check (a failure means the hand count of Lemma 84 is wrong; the orbits are computed by
closure under generators of K, so they are exact and the solver answers still count, but the note
must be corrected):
8. Orbit sizes of R: d2c0 [15, 35, 105, 120, 140, 140, 840] and d2c1 [15, 140, 140, 140, 960] at
   t = 7; [1, 7, 7, 14, 14, 28, 84] and [1, 14, 14, 14, 112] at t = 6; [1, 1, 1, 6, 6] and
   [1, 1, 1, 12] at t = 5; [1] and [1] at t = 4.
9. (Recorded, not graded) "stable": 12 units give as many classes as 24, for every R.

Solver controls (m43a):
10. case_b's (t, k) = (2, 1) example: SAT with a verified model.
11. Every class at t = 4, 5, 6 (dim V = t + 2): UNSAT. UNKNOWN or SKIPPED is not graded.
12. Any SAT at t = 7 must be verified, with rank A_u = 4, rank A_(v_2) = 1 and every rank <= 4.

## Exploratory, with the decision rule

Guesses (low confidence): 40 to 200 classes per form. With A_u fixed, instances behave like the
Case A classes of job m39 (seconds) more than like plain d2 in m40a (over 45 minutes): at least 80
percent of classes decided in this pass, all of them UNSAT.

Rule:
- Every class of both forms UNSAT and every validity check held: **shape (d2) does not occur at rank
  4 for t = 7 and dim V = 9**, computer-assisted, resting on Lemma 78 (delta in R and the hint
  conditions) and Lemma 37. With Corollary 52 (Case A), Lemma 42 (d1) and shape (c) closed (jobs
  m40b to m40d), no element has rank 4.
- UNKNOWN or SKIPPED classes: one more job with at least 3 times the budget each, listed by name from
  grade.json.
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
