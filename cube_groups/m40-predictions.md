# Job m40 (m40a, m40b, m40c, m40d): predictions, written 2026-10-19 ~18:20Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m40.py (Apache-2.0), with
case_b.py, case_b_shapes.py and sat_aniso.py from the repository. Setting: notes/a26.md (Case B at
rank 4 for t = 7 and dim V = 9; the forms of Lemma 37 of case-b-shapes.md at (t, k) = (7, 3); shape
(c) split by the plane Q of Lemma 81 into cY, cX, cG).

## Graded (each must hold; one failure means the encoding or a hand lemma is wrong)

Selfcheck (pure Python, every job):
1. case_b.py's own selfcheck: all graded keys true (Lemma 34; normal form of Lemma 35 on scrambles).
2. case_b_shapes.py's own selfcheck: all graded keys true (census 192 = 24 + 24 + 144 + 0).
3. 7 planes in X_1 = F_2^3, in 3 orbits of sizes 1, 3, 3 under GL_2 on Y fixing e_0; the
   representatives cY, cX, cG lie in the orbits of sizes 1, 3, 3, all different.
4. Unit clauses over sat_aniso.encode(7, 9): 84 + 63 = 147 for each of c, d1, d2c0, d2c1, and
   147 + 14 = 161 for cY, cX, cG; no two unit clauses contradict each other.

Solver controls (m40a):
5. cb_t2_k1 (the example of case-b.md): SAT with a verified model.
6. sh_t3_k2_c, sh_t4_k2_c: UNSAT (A(3) = 3, A(4) = 4; job m12 found both UNSAT).
7. sh_t6_k3_d1, sh_t6_k3_d2c0, sh_t6_k3_d2c1: UNSAT (Lemma 42, Corollary 22; job m12, ~1.5 s each).
8. sh_t7_k3_d1: UNSAT (Lemma 42 holds for every t).
   For 5 to 8, UNKNOWN or ERROR is reported and not graded.
9. Any SAT answer at t = 7 must come with a verified model, every rank <= 4 (Proposition 29(b)),
   dim(X_1 n R) >= 2 in shape c (Corollary 51) and rank A_(v_2) = 1 in shape d2 (Lemma 78).
   An unverified SAT means a bug: stop and fix before reading anything else.

## Exploratory (the question asked), with the decision rule

- m40a: sh_t7_k3_d2c0 and sh_t7_k3_d2c1 (45 minutes each). Prediction: both UNSAT. Confidence:
  moderate (at t = 6 the same forms were UNSAT in 1.5 s; Lemma 78 leaves only a rigid shape).
- m40b, m40c, m40d: shape c with Q = cY, cX, cG (150 minutes each). Prediction: UNKNOWN is the most
  likely outcome for at least one (at t = 6, plain shape c did not finish in 50 minutes, job m12, and
  needed a split by the commuting matrices M_n, jobs m13 to m26). UNSAT for all three is possible.

Rule:
- d2c0 and d2c1 both UNSAT, every graded check held: **shape (d2) does not occur at rank 4 for
  t = 7 and dim V = 9** (row 3 of the table in a24.md), computer-assisted, resting on Lemma 35,
  Lemma 37 and Proposition 27 (which define the forms) and on 2 solver answers without proof
  certificates. Lemma 78 is not used by the CNF.
- cY, cX and cG all UNSAT: shape (c) at rank 4 is closed, resting also on Corollary 51 / Proposition
  27(c4) (d >= 2) and Lemma 81. With Corollary 52 (Case A) and Lemma 42 (d1): **no element of rank 4
  exists, and A(7) <= 8 comes down to the rank-3 configurations (A5), (B6), (B5).**
- Any UNKNOWN: no evidence either way. For shape c, the next step is the split by the commuting
  4 x 4 matrices M_n (Lemma 38 of shape-c.md) inside each Q-class, counted by hand first.
- A verified SAT: an anisotropic system with t = 7 and dim V = 9 exists, so A(7) = 9 (Theorem 29),
  and A(t) = t fails at t = 7. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
