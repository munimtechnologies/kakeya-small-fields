# A sharper restriction at a vector: A(4) = 4, and Z_4^9 x Z_2^2 is settled

MV2 of Munim, Inc., 2026-10-17. Part of kakeya-small-fields version 1.7.10. This note is an
addendum to section 14 of [finite-groups.md](../finite-groups.md) (version 1.7.9); numbering
continues from there (Lemma 30, Theorem 26, Proposition 24, Corollary 17), and the note will be
merged into finite-groups.md in a later version. It was researched and written with AI agents
working in MV2's name. The proofs are by hand; `cube_groups/m6_sharp.py` checks them on examples
and random systems (its unit tests gate this release, and its full run is queued with
pre-registered predictions). No human mathematician has checked the proofs. Text CC BY 4.0, code
Apache-2.0.

## What changes

- **Lemma 30** sharpens Proposition 22(a): in an anisotropic system, an element A_u of rank rho
  gives dim V <= t + A(t - rho - 1) instead of t + A(t - rho). An element of rank t - 1 gives
  dim V <= t.
- **Theorem 26: A(4) = 4 and M(4) = 4** (1.7.9 had 4 <= A(4) <= 5 and M(4) <= 5). So M(t) = t and
  A(t) = t for every t <= 4.
- **Proposition 24** replaces the table of Proposition 23: A(5) <= 6, A(6) <= 8, A(7) <= 10,
  A(8) <= 12, A(9) <= 15 (was 7, 9, 12, 15, 18).
- **Corollary 17** replaces Corollary 16. The question of section 14 is now answered (yes) for a
  self-centralising normal subgroup Z_4^a x Z_2^b whenever b <= 1, a <= max(9, b + 2), or (a, b) is
  one of (10, 4), (10, 5), (10, 6), (11, 6), (10, 7), (11, 7), (11, 8), (12, 8), (12, 9),
  (13, 10). This settles (9, 2), (9, 3) and (9, 4), the first open cases of 1.7.9, and nine more.
- **Prior work**: an order bound of T. J. Laffey (1980) covers every group in the question, with a
  weaker exponent. See the end of this note.

## Setting (from section 14)

X is an F_2-space of dimension t. A *system* is a quadratic map sigma : V -> X with polar form
beta, together with a linear map alpha : V -> End(X), h -> A_h, such that

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Then A_h sigma(h) = 0 for every h (Lemma 21(b)). The system is *anisotropic* if sigma(h) != 0 for
every h != 0, and A(t) is the largest dim V of an anisotropic system with dim X = t; M(t) is the
largest least codimension of a subspace on which sigma vanishes. Known before this note: A(s) = s
for s <= 3 (Lemma 22 and Proposition 21, the latter computed), A is non-decreasing and
superadditive, and max(t, A(t)) <= M(t) <= t + E(t) with E(t) = max over s <= t of
max(A(s) - s, 0) (Theorem 24). We use Lemma 26(a) (a subspace U' with sigma(U') inside a subspace
X' carries a system with values in X', with the maps A_h restricted to X' and projected back onto
it), Lemma 27(a) (a system can be divided by an invariant subspace), Lemma 21(a) (a zero of sigma
in the kernel of alpha lies in the radical of beta, and the system factors through the quotient),
and Lemmas 28 and 29 (an irreducible space of matrices of rank <= 2 with t >= 4 gives dim V <= t;
Lemma 29 uses Theorem 3.5 of C. de Seguins Pazzis, Linear Multilinear Algebra 64 (2016) 1321-1353,
arXiv 1405.1575, which we have not re-proved).

## Lemma 30 (restriction at a vector, sharpened)

**Lemma 30.** Let (sigma, alpha) be a system, u in V, x_0 = sigma(u), phi = beta(u, .), X_1 = ker A_u
and

    U+ = {h in V : beta(u, h) lies in span(x_0)}.

(a) For every h in U+, A_h x_0 = beta(u, h) and A_u sigma(h) = 0.
(b) Let the system be anisotropic, u != 0 and rho = rank A_u. Then codim U+ <= t - 1; sigma(h) is not
in span(x_0) for h in U+ outside span(u); and dim U+ <= 1 + A(t - rho - 1). Hence

    dim V <= t + A(t - rho - 1),

and an element of rank t - 1 gives dim V <= t.

*Proof.* (a) A_u x_0 = 0 (Lemma 21(b)). Put h -> u and h' -> h in (*): A_h x_0 = (I + A_u) phi(h).
For h in U+, phi(h) lies in span(x_0), which A_u kills, so A_h x_0 = phi(h). Put h' -> u in (*):
A_u sigma(h) = (I + A_h) phi(h). This is 0 if phi(h) = 0, and if phi(h) = x_0 it is
x_0 + A_h x_0 = x_0 + x_0 = 0.

(b) phi is linear, and U+ is the preimage of phi(V) n span(x_0). If x_0 lies in phi(V), then
codim U+ = dim phi(V) - 1 <= t - 1. If not, phi(V) != X, and codim U+ = dim phi(V) <= t - 1.

For h, h' in U+, sigma(h) lies in X_1 by (a), and so does beta(h, h') = sigma(h + h') + sigma(h) +
sigma(h'). By Lemma 26(a), U+ carries a system with values in X_1, with the maps
A'_h = (A_h restricted to X_1, projected onto X_1). It is anisotropic. By (a), A'_h x_0 = phi(h) lies
in span(x_0), so span(x_0) is invariant.

If t - rho = 1, then X_1 = span(x_0). Suppose h in U+ is not in span(u) and sigma(h) lies in
span(x_0). Then sigma(h) = x_0, because the system is anisotropic. So A_h x_0 = A_h sigma(h) = 0,
which by (a) means phi(h) = 0, and then sigma(u + h) = x_0 + x_0 + phi(h) = 0 with u + h != 0, a
contradiction. In particular, when t - rho = 1, U+ = span(u), and dim U+ = 1 = 1 + A(0).

If t - rho >= 2, divide by span(x_0) (Lemma 27(a)). This gives a system on U+ with values in
X_1 / span(x_0), of dimension t - rho - 1. Here u is a zero of sigma modulo x_0, and A'_u = 0
because A_u kills X_1. By Lemma 21(a), u lies in the radical of the quotient's polar form, and the
quotient system factors through U+ / span(u). That system is anisotropic by the previous paragraph,
so dim U+ - 1 <= A(t - rho - 1). Finally, dim V = codim U+ + dim U+ <= (t - 1) + 1 + A(t - rho - 1).
QED

Compare Proposition 22(a), which gave dim V <= t + A(t - rho). The gain comes from two facts. Either
phi misses x_0, or the vectors that phi sends to x_0 join U. And x_0 can be divided out of the
restricted system, because u is a zero of the quotient that lies in its kernel.

**Corollary (sharper Corollary 15).** Suppose A(s) = s for every s < t. Then in an anisotropic
system an element of rank rho >= 1 gives dim V <= 2t - rho - 1. So an anisotropic system with
dim V > t needs an irreducible alpha(V) of singular matrices (Corollary 15), and it has no element of
rank t - 1. For t >= 4, it also has an element of rank between 3 and t - 2 (Lemmas 28 and 29).

## Theorem 26 (A(4) = 4)

**Theorem 26.** A(4) = 4 and M(4) = 4. So A(t) = M(t) = t for every t <= 4.

*Proof.* Take an anisotropic system with t = 4 and dim V >= 5. A(s) = s for s <= 3, so by
Corollary 15 alpha(V) is irreducible, its elements are singular, and it does not have the form of
Lemma 28. By Lemma 29 some element has rank >= 3, and since it is singular its rank is 3 = t - 1.
Lemma 30 then gives dim V <= 4, a contradiction. So A(4) <= 4, and A(4) >= 4 from a linear
one-to-one sigma with alpha = 0. Theorem 24 gives M(4) <= 4 + E(4) = 4, and M(4) >= 4 by
Lemma 23(d). QED (computer-assisted through Proposition 21, which gives A(2) and A(3); uses
Theorem 3.5 of de Seguins Pazzis through Lemma 29.)

## Proposition 24 (bounds for larger t)

**Proposition 24.** For every t >= 4,

    A(t) <= min( 2t, max( t + A(t - 4), max over 0 < d < t of M(t - d) + A(d) ) ).

With M(s) <= s + E(s) this gives

    t          1  2  3  4  5  6   7   8   9  10  11  12
    A(t) <=    1  2  3  4  6  8  10  12  15  18  21  24
    E(t) <=    0  0  0  0  1  2   3   4   6   8  10  12

and from t = 12 on it gives only the Chevalley-Warning bound A(t) <= 2t.

*Proof.* Take an anisotropic system with dim V > t. If alpha(V) has an invariant subspace of
dimension d with 0 < d < t, Lemma 27(c) gives dim V <= M(t - d) + A(d). Otherwise alpha(V) is
irreducible (alpha(V) = 0 gives a linear one-to-one sigma, so dim V <= t). If all its elements had
rank <= 2, Lemmas 29 and 28 would give dim V <= t. So some element has rank rho >= 3, and
rho <= t - 1 because it is singular. Lemma 30 and monotonicity give
dim V <= t + A(t - rho - 1) <= t + A(t - 4). The table follows by induction on t. For example,
A(6) <= max(6 + A(2), M(5) + A(1), M(4) + A(2), M(3) + A(3), M(2) + A(4), M(1) + A(5)) =
max(8, 7, 6, 6, 6, 7) = 8. QED (computer-assisted through Proposition 21; uses Theorem 3.5 of de
Seguins Pazzis through Lemma 29.)

For every t from 5 to 11, the term t + A(t - 4) sets the bound in the table, and it comes from
elements of rank 3. An element of rank 4 gives only t + A(t - 5). For t = 5, every other case gives
dim V <= 5. So an anisotropic system with t = 5 and dim V = 6 needs an irreducible space in
M_5(F_2) whose elements all have rank <= 3, some of them rank 3. The same holds for t = 6 and
dim V = 8, for t = 7 and dim V = 10, and for t = 8 and dim V = 12.

## Corollary 17 (the settled cases)

**Corollary 17.** Let L be a finite 2-group whose involutions are all central, with a
self-centralising normal subgroup A ~ Z_4^a x Z_2^b. Suppose b <= 1, or a <= max(9, b + 2), or
(a, b) is one of

    (10, 4), (10, 5), (10, 6), (11, 6), (10, 7), (11, 7), (11, 8), (12, 8), (12, 9), (13, 10).

Then |L| <= |Omega|^4, and the answer to the question of section 14 is yes. This contains
Corollary 16. It settles (9, 2), (9, 3) and (9, 4), the first open cases of 1.7.9, and also
(10, 4), (10, 5), (10, 6), (11, 6), (11, 7), (11, 8), (12, 8), (12, 9) and (13, 10). The first open
cases are now (10, 2),
(10, 3), (11, 4), (11, 5), (12, 6), (12, 7), (13, 8), (13, 9), (14, 10), (14, 11), (15, 12), and
(b + 3, b) for b >= 13.

*Proof.* Repeat the proof of Corollary 14 with the bounds E(t) of Proposition 24. Let tau be the
largest t <= a with E(s) <= b for every s <= t. Then tau >= min(a, 6) when b = 2, min(a, 7) when
b = 3, min(a, 8) when b = 4 or 5, min(a, 9) when b = 6 or 7, min(a, 10) when b = 8 or 9, min(a, 11)
when b = 10 or 11, and min(a, b) when b >= 12 (as E(t) <= t). The condition
(a - tau - 2)(b - 1) <= 1 of that proof then reads: a <= 9 for b = 2 and 3, a <= 10 for b = 4 and 5,
a <= 11 for b = 6 and 7, a <= 12 for b = 8 and 9, a <= 13 for b = 10 and 11, and a <= b + 2 for
b >= 12. QED (computer-assisted through Proposition 21; uses Theorem 3.5 of de Seguins Pazzis
through Lemma 29.)

By the same count, (10, 2) follows from A(7) <= 9, (10, 3) from A(8) <= 11, (11, 4) and (11, 5)
from A(9) <= 9 + b, and (12, 6) and (12, 7) from A(10) <= 10 + b. By the remark after
Proposition 24, A(7) <= 9 and A(8) <= 11 fail only if an irreducible space of matrices of rank
<= 3 in M_7(F_2) or M_8(F_2) carries an anisotropic system of the largest size. So the next step is
the rank-3 term: improve Lemma 30 for elements of rank 3, or classify the irreducible spaces of
matrices of rank <= 3 over F_2 that can occur. A(t) = t for every t would settle every case.

## Computation

`cube_groups/m6_sharp.py` (new in 1.7.10) has three parts.

- **lemma30** checks Lemma 30(a) at sampled vectors of random solutions of (*) with t = 3, 4 and 5.
  The solutions come from random spaces, from spaces spanned by matrices of rank t - 1, and from
  the diagonal system of Lemma 23(d). It also checks all of Lemma 30(b) at every vector of random
  maximal anisotropic subspaces of those solutions. Each subspace is first re-checked to be an
  anisotropic system.
- **cases** checks the table of Proposition 24 and the settled cases of Corollary 17 for every
  a <= 14 and b <= 12.
- **control** makes sure the checks can fail. On random pairs (alpha, sigma) that are not systems,
  part (a) fails. On random anisotropic quadratic maps F_2^3 -> F_2^3 with random alpha, which are
  not systems, sigma(u) lies in beta(u, V) for some u of rank 2, which Lemma 30(b) rules out for
  systems.

The unit tests check Lemma 30 by hand-verified values:

- on Example 1 (ranks 1, 2, 2, and x_0 never in phi(V));
- on a 2-dimensional anisotropic restriction of the diagonal system with t = 2;
- on random systems with t = 3;
- on a pair that is not a system, where (a) fails.

They also check the table and the settled cases. These tests passed before this version was
published. The full run is queued with pre-registered predictions, and its result will be recorded
when finite-groups.md absorbs this note.

## Prior work

T. J. Laffey, "Bounding the order of a finite p-group", Proc. R. Ir. Acad. Sect. A 80 (1980)
131-134, Theorem 1, as quoted by S. Aivazidis and M. Loukaki (J. Algebra 610 (2022) 818-830,
arXiv 2201.07504). It says: if |G| = 2^n, exp G = 2^e and 2^r is the least order of a maximal
elementary abelian normal subgroup of G, then n <= r(3r - 1)/2 + e r. In a 2-group whose
involutions are all central, Omega = Omega_1(L) is elementary abelian and contains every elementary
abelian subgroup. So it is the only maximal one, r = k, and Laffey's theorem gives

    |L| <= 2^(k(3k - 1)/2) |Omega|^e.

The question of section 14 asks for |L| <= 2^k |Omega|^e. The two agree for k = 1 (the generalised
quaternion groups attain both), and the question is stronger for every k >= 2. We have not read
Laffey's paper. Searches on 2026-10-15, 2026-10-16 and 2026-10-17 found no statement of the question
itself. We found nothing on the identity (*) or on A(t) and M(t), so as far as we know Lemma 30 and
Theorem 26 are new. The tools are standard, so a specialist may know them. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
