# Job m49 (m49a, m49b): predictions, written 2026-10-20 ~12:10Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m49.py (Apache-2.0), which
runs m42.py's instances (a copy of the m42.py that jobs m42a, m45a and m45b ran, unchanged) with
the clauses of Corollary 60 added; sat_aniso.py from the repository. Setting: notes/a39.md
(Lemmas 91 and 92, Corollary 60) and notes/a40.md (the results of job m45a).

## Why this job

Corollary 60 says that in every class of (B6) with d >= 1, h -> A_h is one-to-one on N = ker phi.
Once A_u is fixed this is 6 clauses (with 49 auxiliary XOR variables) in (B6). It is the first
hand fact on ker phi that a solver can use directly; whether it helps has never been measured.
Jobs m45b and m45a are the controls: the same CNF without the clauses, the same representatives
and the same solver order, UNKNOWN at 624 s (660 s for pair orbit 8) in every one of these classes.

    m49a   the 13 classes m45b left UNKNOWN with d >= 1 (all but o011_c004, d = 0), 624 s each
    m49b   the 10 classes m45a left UNKNOWN with d >= 1 (all but o012_c001, d = 0), 624 s each

The 13 + 10 are the 2 classes with d = 3 that m45 ran (pairs 0 and 2), the 6 with d = 2 (pairs
4, 5, 6) and 15 with d = 1 (pairs 7 to 10).

## Graded (each must hold)

1. m45.py's check: the classification of (B6) recomputed has 68 classes with m42a's per-pair
   counts, pairs, representatives, kernels and images, and 79 hint conditions.
2. The clauses on a real instance: 6 clauses and 49 auxiliary variables (by hand: 3 non-empty
   subsets S of {1, 2}, two values of e each; one XOR variable per entry for S = {1, 2}); the
   same function gives 14 and 196 for kd = 4 ((B5): 7 subsets, 4 of size >= 2); unit clauses
   consistent; every listed class has d >= 1, with d as in Lemma 83.
3. The clauses against a direct evaluation: on 400 random and constructed choices of
   A_(h_1), ..., A_(h_(kd-1)) (kd = 3 and 4), the clauses hold exactly when every A_n != 0, and
   both outcomes occur.
4. The positive control: the planted system at t = 6 (kd = 3; every A_n on N is non-zero, as its
   A_(a_i) are non-zero projections) is accepted by the CNF with the clauses (6 clauses, 36
   auxiliary variables at t = 6), and the solver finds it SAT and verified (240 s budget; an
   UNKNOWN there is reported, ungraded).
5. Any SAT at t = 7 must be verified (a system, anisotropic, in the normal form, with every
   A_n != 0 on N, rank A_u = 3 and every rank <= 4).

A failure of 1 to 4 means a bug or a transcription error: fix it, re-run as -v2, count nothing.

## Exploratory, with the decision rule

Guess (low confidence: 6 clauses in an instance of tens of thousands): no SAT; m49a 0 to 3 of 13
UNSAT, m49b 0 to 3 of 10. Classes with d = 3 stay UNKNOWN.

Rule (UNSAT counted only where the control was UNKNOWN, which is every class here):
- **m49a + m49b close at least 7 of 23** (m49a needs 4 and m49b 3 to count as helping in that
  batch): Corollary 60 helps. Queue the same for the open (B5) classes with d >= 2 (after m46)
  and for the 29 m47 classes of (B6) with d >= 1, with the same per-class budget.
- **Fewer than 7 of 23:** drop the clause route as a lever; the hand route (a second fixed matrix,
  as Lemma 71 at t = 6, or a new hand fact) comes first. One or two closures are not read as a
  speed-up: changing the CNF changes the solver's search, so a few closures can be chance.
- Every class closed here is UNSAT *given* Corollary 60 (by hand), so it counts towards (B6)
  computer-assisted on top of Lemmas 89 to 92.
- A verified SAT: A(7) = 9; re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
