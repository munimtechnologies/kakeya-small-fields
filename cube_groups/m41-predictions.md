# Job m41 (m41a, m41b): predictions, written 2026-10-19 ~18:45Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m41.py (Apache-2.0), with
case_a.py and sat_aniso.py from the repository. Setting: notes/a26.md, Lemma 82 (the rank-3
configuration (A5) for t = 7 and dim V = 9; A_u unique up to the group G fixing e_0 and keeping
R = span(e_1, e_2, e_3) and P = span(e_0, ..., e_5)).

## Graded (each must hold; one failure means the encoding or a hand count is wrong)

Selfcheck (pure Python, both jobs):
1. 168 candidates A_u (A_u kills e_0, ..., e_3; image R).
2. The orbit of the representative under the 22 generators is all 168 candidates, and stays inside
   them (Lemma 82: one orbit).
3. Every generator is invertible, fixes e_0 and maps R into R and P into P.
4. Unit clauses: 112 for the normal form, 110 more for the hints; no two contradict each other.
5. At t = 5 with case_a's parameters, the encoder gives exactly case_a's CNF for all 9 orbits.
6. The planted system (t = 6) is a system, is anisotropic, has phi(h_1) = phi(h_2) = 0, and its
   assignment satisfies its CNF.

Solver controls (m41a):
7. Planted: SAT with a verified model.
8. t = 5: all 9 orbits UNSAT (Lemma 52; jobs m15 and m39). UNKNOWN or SKIPPED is not graded.
9. Any SAT answer at t = 7 must come with a verified model, rank A_u = 3 and every rank <= 4
   (Proposition 29(a)). An unverified SAT means a bug: stop and fix before reading anything else.

## Exploratory (the question asked), with the decision rule

- m41a: (A5), plain, 140 minutes. m41b: (A5) with the 110 hint clauses, 150 minutes.
- Prediction: both UNSAT. Confidence: low to moderate. At t = 6 every class of (A4) was UNSAT once
  A_u was fixed (job m30), and (A5) has no slack in Lemma 62 (Lemma 79), but the t = 7 CNF is
  larger and nothing beyond A_u and phi is fixed in the plain run.

Rule:
- Plain UNSAT, every graded check held: **no element of rank 3 in (A5) exists in an anisotropic
  system with t = 7 and dim V = 9** (row 5 of the table in a26.md), computer-assisted, resting on
  Proposition 29(c), Lemma 79 (a) (which fixes the normal form), Lemma 82 and 1 solver answer
  without proof certificate. Under the hypothesis of Proposition 29(c) (no element of rank 4).
- Plain UNKNOWN but hint UNSAT: the same, resting also on Lemma 79 (c), (d) and (3); say so.
- UNKNOWN in both: no evidence. Next: fix sigma(v_3) and A_(v_3) up to the stabiliser of A_u, as
  Lemma 71 did at t = 6.
- A verified SAT: an anisotropic system with t = 7 and dim V = 9 exists, so A(7) = 9. Re-check the
  model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
