# Jobs m54a and m54b: predictions, written 2026-10-20 ~16:50Z before either ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m54 (cube_groups/m54.py) splits the kind-graph class of (B6) with d = 3 (pair orbit 2 of job
m42: X_1 = span(e_0, ..., e_3), R = span(e_3, e_2, e_0 + e_1), x0 = e_0 not in R, R not inside
P = span(e_1, ..., e_6); UNKNOWN after about 250 s in job m42b) by the second matrix A_(h_1), into
the 178 classes of Proposition 30 (notes/a42.md), 18 / 94 / 66 by rank on X_1. Batch a is
m52's representatives 0 to 88 (in the order of their union-find roots), batch b 89 to 177. Setting:
notes/a42.md, a43.md, a44.md. When this was written, jobs m52 (the machine check of the class
counts) and m53 (the kind-P class as 40 instances) had not reported; m54 therefore repeats m52's
kind-graph computation as a gate and solves nothing unless it holds.

## Why the split is exhaustive

As for m53 (cube_groups/m53-predictions.md): m42.py's normal form fixes sigma(u) = x0 = e_0,
P, A_u and phi on a basis of V modulo N = ker phi, and nothing on N. A base change in the
stabiliser G of (x0, P, A_u), then a new basis of V with v_1 = n or n + u, keeps it, and by
Proposition 30 brings A_(v_1) to one of 178 representatives. The A_u used is m42b's own
representative of pair orbit 2 (e_4 -> e_3, e_5 -> e_2, e_6 -> e_0 + e_1, the mask 34086976), so
the instances refine exactly the class m42b ran. The change of coordinates from m52's adapted
basis is the permutation Bm: e_0 -> e_3, e_1 -> e_2, e_2 -> e_1, e_3 -> e_4, e_4 -> e_5,
e_5 -> e_6, e_6 -> e_0; it sends m52's x0, P, X_1, R and A_u to m42's.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. Gate: m52's kind-graph computation gives |G| = 12288, 176126 maps, an action that keeps them,
   class sizes dividing 2|G|, and **178 classes, 18 / 94 / 66 by rank on X_1**.
2. Bm respects products and the identity on 200 random pairs, sends m52's x0, P, X_1 and R to
   e_0, span(e_1..e_6), span(e_0..e_3) and span(e_3, e_2, e_0 + e_1), and sends m52's A_u to
   m42b's representative; that A_u has kernel X_1, image R, d = 3, dim(R n P) = 2, x0 not in R.
3. All 178 representatives, in m42's coordinates, are in Adm; they and their sums with A_u are
   356 different maps; the rank on X_1 matches m52's.
4. The instance has m42's 79 hints, 49 added unit clauses, and no contradictory units.
5. Positive control, as in m53: the planted system at t = 6 with A_(v_1) fixed to its own map is
   accepted, rejected with one entry flipped, and SAT and verified within 240 s (an UNKNOWN there
   is reported, ungraded).
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u and A_(v_1)
   as fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rule

Budget per batch: 140 minutes for 89 instances, each an equal share of what is left, at most
95 s (about 23 times what m42b gave the whole class, per batch).

Guess (low confidence; nothing has measured an instance with two matrices fixed at t = 7):
no SAT; **batch a: 55 to 89 of 89 UNSAT**, median time of the UNSATs under 40 s; the slowest are
the 18 classes where A_(h_1) has rank 0 on X_1.

Rule (for the kind-graph class; m53's rule for kind P stands as written):
- **m53 first.** If m53 has reported fewer than 30 of 40 UNSAT before m54a starts, m54a is
  superseded (a newer job m54a-...-v2 with the check only) and the third-matrix split is counted by
  hand first, since the second-matrix split alone would then be known not to close a class at a
  larger budget per instance than m54 has.
- **Batch a 80 to 89 UNSAT, no SAT:** queue batch b unchanged; re-run any open ones of batch a
  with a 10-minute cap.
- **60 to 79:** queue batch b; re-run the open ones with a 10-minute cap.
- **Fewer than 60:** do not queue batch b; count the third-matrix split by hand for the open
  classes of batch a first.
- **All 178 UNSAT over both batches** (with any re-runs): the kind-graph class of (B6) is empty
  (computer-assisted, given Proposition 30 (a), that is Corollary 60 and Lemma 30, and m42's
  hints); (B6) gains one class.
- A verified SAT: a candidate for A(7) = 9; re-check by an independent brute force before any
  claim.

Nothing here measures a speed-up; an UNSAT is a closed case whatever the budget; the solver's
answers are saved without proof certificates.
