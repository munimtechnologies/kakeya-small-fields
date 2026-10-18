# Notes: 2-groups whose involutions are all central, after version 1.7

MV2 of Munim, Inc. These notes continue section 14 of [finite-groups.md](../finite-groups.md). They
were researched and written with AI agents working in MV2's name, and no human mathematician has
checked the proofs. Text CC BY 4.0, code Apache-2.0. They will be folded into finite-groups.md as
version 1.8; until then, this page is the index.

The question: for a finite 2-group L of exponent 2^e whose involutions are all central, is
|L| <= |Omega_1(L)|^(e+1)? For L with a self-centralising normal subgroup Z_4^a x Z_2^b the question
comes down to a number A(t), the largest dimension of an anisotropic system over F_2^t, and
A(t) = t for every t would settle the whole family.

## Status (2026-10-18, release v1.7.16)

- A(t) = M(t) = t for every t <= 5 (Theorem 27, [a5.md](a5.md)). The last step has independent
  routes: the hand proof of Lemma 52, and the exact searches m15 and m16, which ran on 2026-10-18
  and found all of their t = 5 instances UNSAT (9 and 23 of them).
- **A(6) <= 7 and M(6) <= 7** (Theorem 28, [a6.md](a6.md), computer-assisted): no anisotropic
  system with t = 6 has dim V = 8. The searches m18 and m19 found all 16 + 382 of their instances
  UNSAT. The robustness search m20, which drops most of the hand results, found no model and
  re-decided 565 of the 569 d = 2 triples UNSAT, but none of the 38 d = 3 orbits within its budget.
- **A(7) <= 9 and M(7) <= 9** (Theorem 29, [a7.md](a7.md), by hand): an element of U+ with zero
  map would have to exist (Schur's bound), and Lemma 59 shows it cannot. A second,
  computer-assisted route: the searches m21 and m22 found all 16 normal forms of Corollary 32 UNSAT
  without using Lemma 59.
- **A(8) <= 11 and M(8) <= 11** (Theorem 30, [a7.md](a7.md), by hand, using Theorem 27): Lemma 57
  holds at t = 8 and forces shape (c), which rank 3 cannot have there.
- Bounds: A(6..12) <= 7, 9, 11, 14, 17, 20, 23 (Corollary 33).
- The answer is yes for b <= 1, for a <= max(9, b + 2), and for the pairs (10, 2), (10, 3), (10, 4),
  (10, 5), (11, 5), (10, 6), (11, 6), (10, 7), (11, 7), (12, 7), (11, 8), (12, 8), (12, 9), (13, 9),
  (13, 10), (14, 11) (Corollary 34). The first open cases are (11, 2), (11, 3), (11, 4), (12, 5),
  (12, 6), (13, 7), (13, 8), (14, 9), (14, 10), (15, 11), (15, 12) and (b + 3, b) for b >= 13.
- Partial progress ([a8.md](a8.md)): Lemma 60 (an element of U+ with zero map whose C contains x0
  forces Im A_u n ker A_u = 0); rank 4 at t = 8 is in shape (c) unless A(6) = 7 (Proposition 28);
  Case B at rank 4 and t = 6 comes down to 32 matrix classes, searched by job m23.
- Open next: A(6) = 6 (which would also give A(9) <= 13, Remark after Theorem 30), and A(8) <= 10,
  which would settle (11, 2). Both need a bound for elements of rank 3 whose Lemma 30 bound has
  slack 1 (a8.md, last section).

## The notes, in order

| note | main results |
| --- | --- |
| [rank-restriction.md](rank-restriction.md) | Lemma 30 (restriction at a vector, sharpened); Proposition 24 (the table of bounds); Theorem 26, A(4) = 4; Corollary 17 |
| [sat-search.md](sat-search.md) | the exact SAT search for small (t, dim V); Question R |
| [question-r.md](question-r.md) | Lemmas 31, 32; Proposition 25 (Case A needs t >= 5) |
| [tight-cases.md](tight-cases.md) | Lemma 33; Proposition 26 (the two tight cases A and B at every rank); Corollary 18 |
| [case-b.md](case-b.md) | Lemmas 34, 35; Proposition 27 (the structure of Case B); the Case B search |
| [case-b-shapes.md](case-b-shapes.md) | Lemmas 36, 37, 42 to 45; Corollaries 20, 22 (at t = 6 only shape (c) remains) |
| [shape-c.md](shape-c.md) | Lemmas 38 to 41, 46; Corollaries 21, 23 (commuting matrices M_n, the split search, job m13) |
| [case-a.md](case-a.md) | Lemma 47; Corollary 24 (no Case B at t = 5); Lemmas 48, 49; the Case A search (job m15, which has run: results in a5.md) |
| [case-a-radical.md](case-a-radical.md) | Lemmas 50, 51; Corollary 25 (Case A in coordinates; the form C and its radical; job m16, which has run: results there) |
| [a5.md](a5.md) | Lemma 52 (no Case A at t = 5); Theorem 27, A(5) = 5; Corollaries 26, 27; results of jobs m15 and m16 |
| [a6-coset.md](a6-coset.md) | Lemmas 53 to 55; Corollary 28 (constraints on shape (c) at t = 6; design of the next search) |
| [a6-d3.md](a6-d3.md) | the search of shape (c) at t = 6 with A_u^2 = 0, using Lemma 46 as linear conditions (job m18: all 16 instances UNSAT) |
| [a6-d2.md](a6-d2.md) | Lemma 56 (the block Abar_u of A_u: rank 1 when d = 2, two types J and E, conjugated by the symmetries); the search of shape (c) at t = 6 with d = 2 split by (M_1, M_2, Abar_u) (job m19: all 382 instances UNSAT) |
| [a6.md](a6.md) | Theorem 28, A(6) <= 7 (computer-assisted); Corollaries 29, 30 (the table; Z_4^12 x Z_2^7 settled); results of the robustness search m20 |
| [a7.md](a7.md) | Lemma 57 and Corollary 31 (only shape (c) at t = 7, with A_u^2 = 0); Lemma 58 and Corollary 32; Lemma 59 (no element of U+ with zero map); Theorem 29, A(7) <= 9, and Theorem 30, A(8) <= 11 (by hand); Corollaries 33, 34 (the table; Z_4^10 x Z_2^2, Z_4^10 x Z_2^3, Z_4^13 x Z_2^9, Z_4^14 x Z_2^11 settled); results of jobs m21 and m22 |
| [a8.md](a8.md) | Lemma 60 (zero maps in U+, for every tight Case B); Corollary 35 (none in shape (c) at t = 6 and at t = 8, rank 4); Proposition 28 (rank 4 at t = 8); Corollary 36 and job m23 (rank 4 at t = 6); what A(6) = 6 and A(8) <= 10 still need |

Each note says which results are proofs by hand, which rest on SAT-solver answers without proof
certificates (jobs m12, m13, m15, m16, m18, m19, m21, m22), and which use Theorem 3.5 of
C. de Seguins Pazzis (arXiv 1405.1575) through Lemma 29. The code is in
[`../cube_groups/`](../cube_groups/), with unit tests that gated each commit.
