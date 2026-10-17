# Question R at every rank: the two tight cases, and Case A is impossible when 2 rho <= t

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10, next to
[question-r.md](question-r.md) and [sat-search.md](sat-search.md). Numbering continues from
question-r.md (Lemma 33, Proposition 26, Corollary 18). This is partial progress: it settles no new
case of Corollary 17, but it reduces the next two cases to one configuration. It was researched and
written with AI agents working in MV2's name. The proofs are by hand; `cube_groups/tight_cases.py`
checks Lemma 33 exhaustively for t <= 6, and its unit tests gated this commit. No human
mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

## What changes

- **Proposition 26** extends the two cases A and B of question-r.md from rank t - 2 to every rank
  rho, and shows that **Case A needs 2 rho >= t + 1**. For rank t - 2 this is the bound t >= 5 of
  Proposition 25.
- **Corollary 18.** Rank 3 is what holds up Proposition 24 from t = 5 to t = 11. At t = 6 and t = 7
  only Case B is left: A(6) <= 7 holds unless some anisotropic system with t = 6 and dim V = 8 has a
  rank-3 element in Case B, and A(7) <= 9, which would settle Z_4^10 x Z_2^2 (the first open case of
  Corollary 17), holds unless some system with t = 7 and dim V = 10 has one.

## Setting

As in section 14 of [finite-groups.md](../finite-groups.md) and in
[rank-restriction.md](rank-restriction.md): X = F_2^t, a quadratic map sigma : V -> X with polar
form beta, and a linear map h -> A_h from V to End(X) with

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

A(t) is the largest dim V of an anisotropic system (sigma(h) != 0 for h != 0); A(s) = s for s <= 4
(Theorem 26). For u in V put x0 = sigma(u), phi = beta(u, .), X_1 = ker A_u, R = Im A_u and
U+ = {h : phi(h) in span(x0)}. Lemma 30 says that for an anisotropic system and an element u != 0 of
rank rho, with k = t - rho,

    dim V = codim U+ + dim U+ <= (t - 1) + (1 + A(k - 1)) = t + A(k - 1).

Question R (sat-search.md) asks whether t + A(k - 2) holds instead.

## Lemma 33 (linear algebra)

**Lemma 33.** Let 1 <= k <= t - 1, let A_u in M_t(F_2) have rank t - k, let x0 be a non-zero vector
of X_1 = ker A_u, and let R = Im A_u. Let A_v satisfy A_v x0 = x0 and Im(I + A_v) in R, and put
A_w = A_u + A_v. If A_v and A_w both have rank <= t - k, then t >= 2k + 1. If t = 2k + 1, their
kernels K_v and K_w have dimension k, they meet in a space of dimension k - 1 inside X_1, and
K_v + K_w = R.

*Proof.* I + A_v is the identity on K_v, so K_v lies in Im(I + A_v), which lies in R. Also
I + A_w = A_u + (I + A_v) has its image in R, and the same argument puts K_w in R. On K_v n K_w,
A_u = A_v + A_w vanishes, so K_v n K_w lies in X_1. It does not contain x0, because A_v x0 = x0 != 0.
So dim (K_v n K_w) <= k - 1. The ranks are at most t - k, so dim K_v >= k and dim K_w >= k. Then

    k + 1 <= dim K_v + dim K_w - dim (K_v n K_w) = dim (K_v + K_w) <= dim R = t - k,

so t >= 2k + 1. If t = 2k + 1, every step is an equality. QED

For k = 2 this is the counting step of Lemma 32 in question-r.md. That lemma had one more
hypothesis (A_v kills a second vector z of X_1), which Lemma 33 does not need.

## Proposition 26 (the tight cases)

**Proposition 26.** Let 1 <= rho <= t - 2, put k = t - rho, and suppose A(s) = s for every s <= k - 1
(true for k <= 5). Let (sigma, alpha) be an anisotropic system with dim V = t + k - 1 and an element u
of rank rho. Then:

(a) every A_h has rank <= rho;
(b) codim U+ = t - 1 and dim U+ = k;
(c) either phi maps V onto X (**Case A**), or phi(V) is a hyperplane that does not contain x0 and
    U+ = ker phi (**Case B**);
(d) in Case A, t >= 2k + 1, that is 2 rho >= t + 1;
(e) in Case B, every h in U+ has A_h x0 = 0, sigma(h) in X_1 and Im A_h in R, and sigma(U+) spans
    X_1.

*Proof.* (a) If h != 0 had rank rho' > rho, Lemma 30 for h would give
dim V <= t + A(t - rho' - 1) <= t + A(k - 2) = t + k - 2, as A is non-decreasing. Every A_h with
h != 0 is singular (A_h sigma(h) = 0 with sigma(h) != 0), so the rank t of an invertible matrix does
not occur, and A_0 = 0.

(b) The display above with A(k - 1) = k - 1 reads dim V <= t + k - 1, so both of its inequalities
are equalities.

(c) As in the proof of Lemma 30: if x0 lies in phi(V), then codim U+ = dim phi(V) - 1, which is
t - 1 only if phi(V) = X. If not, codim U+ = dim phi(V) = t - 1, and U+ is the preimage of
phi(V) n span(x0) = 0, that is ker phi.

(d) Take v with phi(v) = x0. Then v is in U+, so A_v x0 = phi(v) = x0 by Lemma 30(a). Lemma 31
applies to (u, v), because beta(u, v) = x0 = sigma(u), and as phi(V) = X it gives
Im(I + A_v) in R. By (a), A_v and A_w = A_(u + v) have rank <= rho = t - k. A_u has rank t - k and
kills x0 (Lemma 21(b)). Lemma 33 gives t >= 2k + 1.

(e) Let h be in U+ = ker phi. Lemma 30(a) gives A_h x0 = phi(h) = 0 and A_u sigma(h) = 0, so sigma(h)
lies in X_1. The polarised form of (*) (the proof of Lemma 31) with h_1 = u and h_2 = h reads
A_(h') beta(u, h) = A_u beta(h, h') + A_h phi(h'). Here beta(u, h) = 0, so A_h phi(h') = A_u beta(h, h')
lies in R for every h'. So A_h maps phi(V) into R and kills x0, and X = phi(V) + span(x0), so
Im A_h lies in R. Finally, if sigma(U+) spanned a proper subspace Y of X_1, then U+ would carry an
anisotropic system with values in Y (Lemma 26(a)), so k = dim U+ <= A(dim Y) = dim Y < k. QED

So in a system of this size, every element of rank rho is in Case A or Case B, and when 2 rho <= t,
every one of them is in Case B.

## Corollary 18 (Question R reduces to Case B)

**Corollary 18.** Let 1 <= rho <= t - 2 and k = t - rho, with A(s) = s for every s <= k - 1.

(a) Question R holds for elements of rank rho in X = F_2^t (dim V <= t + A(k - 2) = t + k - 2) if
    and only if no anisotropic system with dim V = t + k - 1 has an element of rank rho. If
    2 rho <= t, it holds if and only if no such system has an element of rank rho in Case B.
(b) A(6) <= 7 holds if and only if no anisotropic system with t = 6 and dim V = 8 has an element of
    rank 3 in Case B. A(7) <= 9 holds if and only if no anisotropic system with t = 7 and dim V = 10
    has an element of rank 3 in Case B. A(7) <= 9 settles Z_4^10 x Z_2^2.

*Proof.* (a) A system with a larger V and an element u of rank rho restricts (Lemma 26(a), with
X' = X) to a subspace of dimension t + k - 1 that contains u. The rest is Proposition 26(c) and (d).

(b) Take t = 6 and dim V = 8, or t = 7 and dim V = 10. By the proof of Proposition 24, a reducible
alpha(V) gives dim V <= max over 0 < d < t of M(t - d) + A(d), which is 7 for t = 6 (computed there)
and 9 for t = 7 (the terms are 9, 8, 7, 7, 8, 9 for d = 1, ..., 6, with M(s) <= s + E(s) and the
table of Proposition 24). An irreducible alpha(V) whose elements all have rank <= 2 gives
dim V <= t (Lemmas 28 and 29). So some element has rank >= 3. Rank >= 4 gives dim V <= t + A(t - 5),
which is 7 for t = 6 and 9 for t = 7 (Lemma 30). So the element has rank 3, and with k = t - 3 the
system has dim V = t + k - 1. A(s) = s holds for s <= k - 1 (that is, s <= 2 and s <= 3). Since
2 x 3 <= t, (a) puts the element in Case B. Conversely, such a system has dim V = 8 > 7, or
10 > 9. The remark after Corollary 17 in rank-restriction.md says that (10, 2) follows from
A(7) <= 9. QED (uses Theorem 3.5 of de Seguins Pazzis through Lemma 29,
and Proposition 21 through A(2) and A(3), as Proposition 24 does.)

For t = 5 and rank 3 (k = 2), 2 rho = 6 > 5, so Case A is not excluded; Proposition 25 describes
the only shape it can have. Case B is open for every t >= 4. Question R at rank 3 for t = 8 is also
reduced to Case B (k = 5 needs A(4) = 4, which holds). From t = 9 on, Proposition 26 needs A(5) = 5,
which is open.

## What Case B looks like

In Case B, U+ = ker phi has dimension k, and its elements form a k-dimensional space of matrices
that kill x0 and map X into R, which has dimension rho. sigma maps U+ into X_1, so on U+ it is an
anisotropic system of dimension k = dim X_1. The counting of Lemma 33 needs an element v with
Im(I + A_v) in R, and Case B has no vector v with phi(v) = x0 to supply one. This is the gap.

**Remark (k = 2).** In Case B with k = 2, Im A_u meets ker A_u. *Proof.* U+ = span(u, v) with
beta(u, v) = 0, and z = sigma(v) lies in X_1 outside span(x0) (it is not 0 or x0, as sigma(v) and
sigma(u + v) = x0 + z are not 0). By (e), A_v kills x0, and A_v z = A_v sigma(v) = 0, so A_v kills
X_1. phi(V) is a hyperplane that misses x0, so it meets X_1 in a line span(y); take w with
phi(w) = y. With h_1 = u, h_2 = v and h' = w, the polarised form of (*) gives
A_u beta(v, w) = A_v phi(w) = A_v y = 0, so beta(v, w) lies in X_1. Putting h -> u, h' -> w and
h -> v, h' -> w in (*) gives A_w x0 = (I + A_u) y = y and A_w z = (I + A_v) beta(v, w) = beta(v, w),
so A_w maps X_1 into itself. Putting h' -> u in (*) gives A_u sigma(w) = (I + A_w) y, which lies in
X_1 n R. If it were 0, sigma(w) would lie in X_1, and so would every value of sigma and beta on
span(u, v, w) (beta(u, w) = y, beta(v, w) and beta(u, v) = 0 are in X_1). Then span(u, v, w) would
carry an anisotropic system of dimension 3 with values in X_1 (Lemma 26(a)), against A(2) = 2. QED

We have found no contradiction in Case B.

## Computation

`cube_groups/tight_cases.py` checks Lemma 33 by exhaustive search. A change of basis that fixes
x0 = e_0 puts X_1 in the form span(e_0, ..., e_(k-1)), and then R in one of a few normal forms, one
for each dimension d of R n X_1 and each answer to "is x0 in R?". Then A_u runs over the matrices
whose first k columns are zero and whose other columns are an ordered basis of R, and A_v over the
matrices with column 0 equal to e_0 and column j equal to e_j + r_j (r_j in R) for j >= 1. These are
exactly the pairs that satisfy the hypotheses before the rank conditions. The unit tests (which
gated this commit) assert:

- for (t, k) = (3, 2), (4, 3), (5, 3), (5, 4), (6, 4) and (6, 5), where t < 2k, that no A_v has
  rank <= t - k at all, out of 12, 24, 1,280, 48, 5,120 and 96 candidates;
- for (t, k) = (4, 2) and (6, 3), where t = 2k, that exactly 8 and 192 of the 256 and 196,608
  candidate A_v have rank <= k, as the proof predicts, and that none of them survives with any of the
  6 and 168 matrices A_u, so the pair argument is needed and works;
- for (t, k) = (5, 2), that pairs satisfying every hypothesis exist, with every conclusion,
  including the example of question-r.md;
- on a pair with t = 4 and k = 2 whose only failing hypothesis is Im(I + A_v) in R, that the
  hypothesis is needed.

## Prior work

As for rank-restriction.md and question-r.md: searches on 2026-10-15 to 2026-10-17 found nothing on
the identity (*), on A(t) or on Question R. The tools are elementary, so a specialist may know
them. Please open an issue at https://github.com/munimtechnologies/kakeya-small-fields if so, or
if you find an error.
