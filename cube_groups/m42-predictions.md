# Job m42 (m42a to m42d): predictions, written 2026-10-19 ~19:50Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m42.py (Apache-2.0), with
sat_aniso.py from the repository. Setting: notes/a27.md, Lemma 83 (the rank-3 configurations (B6)
and (B5) for t = 7 and dim V = 9, shape ("B", p) with p = 6 and p = 5; the pairs
(ker A_u, Im A_u) up to G = {g : g e_0 = e_0, g P = P}).

## Graded (each must hold)

Validity checks (a failure means a bug: fix, re-run as -v2, count nothing from that job):
1. Subspace counts 1395, 11811, 155, 1395, 7, 35, 1, 3, every one in reduced echelon form.
2. |G| by formula: 20158709760 (t = 7, p = 6), 639959040 (7, 5), 9999360 (6, 5), 645120 (6, 4),
   168 (4, 3), 48 (4, 2), 1 (2, 1); at t = 2 and 4 also by enumeration.
3. Every transvection generator lies in G; every random unit lies in its stabiliser.
4. At t = 2 and t = 4 (p = 3 and 2): the computed pair orbits are exactly the G-orbits, |H| times
   the orbit size is |G|, and the computed classes are exactly the H-orbits.
5. At t = 6 and 7: the pair-orbit sizes add up to (number of X_1) x (number of R), each divides |G|;
   in every pair the class sizes add up to 168, every member has kernel X_1 and image R, and each
   class size divides |G| / (pair-orbit size). Every t = 7 representative has rank 3.
6. Hint conditions: 79 (B6), 111 (B5), 14 and 26 (t = 4, p = 3 and 2), 0 (t = 2), 45 (planted);
   no two unit clauses contradict; 112 unit clauses for the normal form at t = 7.
7. The planted system (t = 6) is a system, anisotropic, has phi(h_1) = phi(h_2) = 0, rank A_u = 3,
   x0 outside P, and its assignment satisfies its CNF with the hints.

Agreement checks (a failure means a hand count in Lemma 83 is wrong or the random generators
missed part of a group; the split stays complete, because each computed orbit lies inside one true
orbit, so solver answers still count, but the note must be corrected):
8. Pair orbits: 13 (t = 7, p = 6), 49 (7, 5) with 20 for the 155 X_1 inside L + P and 29 for the
   1240 others, 11 (6, 5), 39 (6, 4) with 18 and 21, 7 (4, 3) of sizes 7, 21, 21, 28, 42, 42, 84,
   19 (4, 2), 3 (2, 1).
9. Classes at t = 6: 66 for p = 5 and 401 for p = 4, the counts of job m30.
10. (Recorded, not graded) "stable": 32 generators give as many classes as 64, in every pair.

Solver controls (m42a):
11. Planted: SAT with a verified model.
12. t = 2, p = 1: SAT (verified) exactly for R = span(e_1), UNSAT for the other two pairs.
13. t = 4, dim V = 5, p = 3 and p = 2: every class UNSAT (A(4) = 4). UNKNOWN or SKIPPED is not
    graded.
14. Any SAT at t = 7 must be verified, with rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rule

Guesses: B6 has 60 to 150 classes, B5 has 250 to 700. B5 behaves like (B4) at t = 6 (most UNSAT in
seconds): at least 70 percent decided in this pass. B6 behaves like (B5) at t = 6 (40 percent
decided at one minute there): 20 to 60 percent decided. Confidence: low; nothing at t = 7 with
rank 3 has been timed.

Rule:
- Every class of a shape UNSAT and every validity check held: **no anisotropic system with t = 7
  and dim V = 9 has an element of rank exactly 3 in that shape**, computer-assisted. This does not
  need "no element of rank 4": the instances fix only u.
- Both shapes closed, with (A5) closed (job m41) and no element of rank 4 (jobs m39, m40):
  A(7) <= 8 (Theorem 33 candidate). Write it up only after re-reading every dependency.
- UNKNOWN or SKIPPED classes: one more job with at least 3 times the budget each; if still open,
  split by a second fixed matrix (as Lemma 71 at t = 6), designed in a note first.
- A verified SAT: A(7) = 9. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
