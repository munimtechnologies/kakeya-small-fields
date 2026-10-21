# Job m44 (m44a to m44d): predictions, written 2026-10-19 ~22:10Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m44.py (Apache-2.0), with
sat_aniso.py, case_b.py and case_b_shapes.py from the repository. Setting: notes/a29.md, Lemma 85
(shape (c) of Case B at rank 4 for t = 7 and dim V = 9; the image R = Im A_u, with
dim(R n W) >= 2 by Corollary 51, up to K = {g : g e_0 = e_0, g W = W, g P = P}, then A_u up to the
stabiliser of R; the matrices M_1, M_2 of Lemma 38 as conditions).

## Graded (each must hold)

Validity checks (a failure means a bug: fix, re-run as -v2, count nothing from that job):
1. Unit tests pass (including the hint clauses on hand-made data at t = 6: they hold for
   (M_1, M_2) = (N, N^2) and fail for (N, N), for a non-commuting pair and for a wrong A_(v_1)); the
   selfchecks of case_b.py and case_b_shapes.py pass.
2. |K| by formula: 576, 64512, 30965760 for t = 5, 6, 7; at t = 5, 6 also by enumeration.
3. Every transvection generator lies in K; every random unit lies in the stabiliser of its R.
4. The subspaces R of dimension t - 3 with dim(R n W) >= 2 number 7, 99, 995 for t = 5, 6, 7; the
   orbit sizes add up to these, each dividing |K|.
5. At t = 5, 6: |Stab(R)| x (orbit size) = |K| for every representative, and the computed classes
   of A_u are exactly the orbits of the whole stabiliser.
6. At t = 7: in every orbit of R the class sizes add up to 20160, every member has kernel W and image
   R, each class size divides |K| / (orbit size); every representative has rank 4.
7. Linear conditions 40, 75, 120 and 6 non-zero clauses for t = 5, 6, 7; unit clauses for A_u: 10,
   18, 28; no two unit clauses contradict.

Agreement checks (a failure means a hand count of Lemma 85 is wrong; orbits are computed by closure
under generators of K and classes are checked to be complete, so the solver answers still count, but
the note must be corrected):
8. One orbit per type, with sizes: t = 7: W 15, YP 35, Yn 105, X 420, G 420; t = 6: W 1, YP 7, Yn 7,
   X 42, G 42; t = 5: YP 1, X 3, G 3.
9. Classes of A_u when R contains W: 1 at t = 6 (exact), 5 at t = 7.
10. (Recorded, not graded) "stable": 12 units give as many classes as 24, for every R.

Solver controls (m44a):
11. case_b's (t, k) = (2, 1) example: SAT with a verified model.
12. Every class at t = 5, 6 (dim V = t + 2): UNSAT. UNKNOWN or SKIPPED is not graded.
13. Any SAT at t = 7 must be verified, with rank A_u = 4, every rank <= 4 and dim(X_1 n R) >= 2.

## Exploratory, with the decision rule

Guesses (low confidence): 15 to 80 classes in all. Fixing the whole of A_u and adding Lemma 38 makes
the instances much smaller than m40b's (150 minutes, UNKNOWN), but the stabilisers of A_u stay large
(R containing W has a stabiliser of order 2064384 in K), so some classes may stay open. Guess: at
least half of the classes decided in this pass, all of them UNSAT.

Rule:
- Every class UNSAT and every validity check held: **shape (c) does not occur at rank 4 for t = 7
  and dim V = 9**, computer-assisted, resting on Lemmas 35 and 37 (the form), Corollary 51 (dim(R n W)
  >= 2 and n -> A_n one-to-one; it uses A(6) <= 7), Lemma 38 (the conditions (S), (a), (b), proved by
  hand from (*) and (Q)) and Lemma 85 (by hand; the orbit closure checks it).
- With Corollary 52 (Case A), Lemma 42 (d1) and shape (d2) closed (job m43): no element of rank 4,
  and A(7) <= 8 comes down to (B6) and (B5) (job m42), as (A5) is closed (Corollary 53, job m41).
- UNKNOWN or SKIPPED classes: one more job with at least 3 times the budget each, listed by name from
  grade.json; if those stay open, split further by (M_1, M_2) up to the stabiliser of A_u.
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
