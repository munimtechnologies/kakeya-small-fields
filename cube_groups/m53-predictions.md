# Job m53: predictions, written 2026-10-20 ~15:40Z before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m53 (cube_groups/m53.py) splits the kind-P class of (B6) with d = 3 (pair orbit 1 of job m42,
UNKNOWN after about 250 s in job m42b) by the second matrix A_(h_1), into the 40 classes of
Proposition 30 (notes/a42.md). Setting: notes/a42.md and notes/a43.md. When it was written, job
m52 (the machine check of the class counts) had not reported; m53 therefore repeats m52's kind-P
computation as a gate and solves nothing unless it holds.

## Why the split is exhaustive

m42.py's normal form fixes sigma(u) = x0 = e_0, P = span(e_1, ..., e_6), A_u, and the basis of V
modulo N = ker phi through phi(v_(2 + j)) = e_j. It does not fix v_1, v_2, sigma or beta on N, or
anything else. A base change g with g x0 = x0, g P = P, g A_u = A_u g, followed by a new basis of V
(v_0 = u; v_1 = n or n + u; v_2 completing N; v_(2 + j) with phi = e_j again), keeps the normal
form. By Proposition 30 (a) every n in N outside span(u) has A_n in Adm, and by (b), (c) such a
g and the choice between n and n + u bring A_(v_1) to one of 40 representatives. So the kind-P
class is empty if and only if all 40 instances are unsatisfiable. A_u here is e_4 -> e_1,
e_5 -> e_2, e_6 -> e_3 rather than m42b's representative; pair orbit 1 is a single class of A_u
(m42a's classification, checked again by m45; Lemma 82), so either choice is valid.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. Gate: m52's kind-P computation gives |G| = 86016, 176126 maps, an action that keeps them, class
   sizes dividing 2|G|, and **40 classes, 6 / 20 / 14 by rank on X_1** (Proposition 30 (c)).
2. The change of coordinates (e_k -> e_(k + 1), e_6 -> e_0) respects products and the identity on
   200 random pairs, and sends m52's A_u to the A_u above; that A_u has kernel span(e_0..e_3) and
   image span(e_1, e_2, e_3) (d = 3, R inside P, x0 not in R).
3. All 40 representatives, in m42's coordinates, are in Adm (kill e_0, image in R, rank <= 2 on
   X_1, not 0, not A_u); the 40 and their sums with A_u are 80 different maps; the rank on X_1
   matches m52's.
4. The instance has m42's 79 hints, 49 added unit clauses, and no contradictory units.
5. Positive control: the planted system at t = 6 with A_(v_1) fixed to its own map is accepted by
   the CNF and rejected when one entry is flipped, and the solver finds it SAT and verified within
   240 s (an UNKNOWN there is reported, ungraded).
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u and A_(v_1)
   as fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rule

Budget: 140 minutes for the 40 instances, each an equal share of what is left, at most 210 s.

Guess (low confidence): no SAT; **28 to 40 of 40 UNSAT**, median time of the UNSATs under 60 s;
the slowest are the 6 classes where A_(h_1) has rank 0 on X_1 (A_(h_1) then only maps a
complement of X_1 into R, so it adds the fewest linear conditions to (*) and (N)).

Rule:
- **40 of 40 UNSAT:** the kind-P class of (B6) is empty (computer-assisted, given Proposition 30
  (a), that is Corollary 60 and Lemma 30, and m42's hints); (B6) goes to 15 of 68 closed. Next:
  the same split for kind graph (178 classes, pair orbit 2) in two jobs, then kind L (308 classes
  by hand in a43.md, if m52 agrees).
- **30 to 39 UNSAT, no SAT:** the split works; re-run the open ones with a 15-minute cap, then
  kind graph.
- **Fewer than 30:** the split alone is not enough at this budget; count the third-matrix split
  (A_(h_2) up to the stabiliser of A_u and A_(h_1)) by hand for the open classes before any longer
  run.
- A verified SAT: a candidate for A(7) = 9; re-check by an independent brute force before any
  claim.

Nothing here measures a speed-up: the 40 instances get about 34 times the total time m42b gave
the whole class. An UNSAT is a closed case whatever the budget; the solver's answers are saved
without proof certificates.
