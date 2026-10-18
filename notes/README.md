# Notes: 2-groups whose involutions are all central, after version 1.7

MV2 of Munim, Inc. These notes continue section 14 of [finite-groups.md](../finite-groups.md). They
were researched and written with AI agents working in MV2's name, and no human mathematician has
checked the proofs. Text CC BY 4.0, code Apache-2.0. They will be folded into finite-groups.md as
version 1.8; until then, this page is the index.

The question: for a finite 2-group L of exponent 2^e whose involutions are all central, is
|L| <= |Omega_1(L)|^(e+1)? For L with a self-centralising normal subgroup Z_4^a x Z_2^b the question
comes down to a number A(t), the largest dimension of an anisotropic system over F_2^t, and
A(t) = t for every t would settle the whole family.

## Status (2026-10-18, release v1.7.13)

- A(t) = M(t) = t for every t <= 5 (Theorem 27, [a5.md](a5.md)). The last step has independent
  routes: the hand proof of Lemma 52, and the exact searches m15 and m16, which ran on 2026-10-18
  and found all of their t = 5 instances UNSAT (9 and 23 of them).
- Bounds: A(6..12) <= 8, 10, 12, 14, 18, 21, 24 (Corollary 26).
- The answer is yes for b <= 1, for a <= max(9, b + 2), and for the pairs (10, 4), (10, 5), (11, 5),
  (10, 6), (11, 6), (10, 7), (11, 7), (11, 8), (12, 8), (12, 9), (13, 10) (Corollary 27). The first
  open cases are (10, 2), (10, 3), (11, 4), (12, 5), (12, 6), (12, 7), (13, 8), (13, 9), (14, 10),
  (14, 11), (15, 12) and (b + 3, b) for b >= 13.
- A(6) <= 7 holds if and only if no anisotropic system with t = 6 and dim V = 8 has an element of
  rank 3 in Case B of shape (c) (Corollaries 18 and 22). This is open. Shape (c) splits by
  d = dim(X_1 n R) in {2, 3}. Both halves have a search queued with its predictions written first:
  d = 3 (job m18, [a6-d3.md](a6-d3.md)) and d = 2 (job m19, [a6-d2.md](a6-d2.md), by the triple
  (M_1, M_2, Abar_u) of Lemma 56).

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
| [a6-d3.md](a6-d3.md) | the search of shape (c) at t = 6 with A_u^2 = 0, using Lemma 46 as linear conditions (job m18) |
| [a6-d2.md](a6-d2.md) | Lemma 56 (the block Abar_u of A_u: rank 1 when d = 2, two types J and E, conjugated by the symmetries); the search of shape (c) at t = 6 with d = 2 split by (M_1, M_2, Abar_u) (job m19) |

Each note says which results are proofs by hand, which rest on SAT-solver answers without proof
certificates (jobs m12, m13, m15, m16), and which use Theorem 3.5 of C. de Seguins Pazzis (arXiv
1405.1575) through Lemma 29. The code is in [`../cube_groups/`](../cube_groups/), with unit tests that
gated each commit.
