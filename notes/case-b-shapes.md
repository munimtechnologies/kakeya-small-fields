# Case B by shape: a shared-kernel lemma, rank bounds in shape (d2), and a split search

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10, next to
[case-b.md](case-b.md), [tight-cases.md](tight-cases.md) and [sat-search.md](sat-search.md).
Numbering continues from case-b.md (Lemma 36, Lemma 37, Corollary 20). This is partial progress:
it settles no new case of Corollary 17. It was researched and written with AI agents working in
MV2's name. The proofs are by hand; `cube_groups/case_b_shapes.py` checks the case split of
Proposition 27 exhaustively on the systems that U+ carries, and its unit tests gated this commit.
No human mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

## What changes

- **Lemma 36.** Two elements of rank rho in Case B with the same kernel, one inside the other's U+,
  have the same U+ whenever beta(n, U+) lies in span(sigma(n)).
- **Corollary 20.** In shape (d2) of Proposition 27, A_(n_2) has rank at most rho - 1. If
  A_(u + n_2) has rank rho, then delta lies in beta(u, V) and u + n_2 is in shape (d2) too, with the
  same n_2. So when delta + x0 lies in beta(u, V) instead, A_(n_2) and A_(u + n_2) both have rank at
  most rho - 1. This narrows shape (d2) but does not rule it out.
- **Lemma 37** fixes, in the normal form of Lemma 35, also a basis of U+ and its values, one way for
  each shape. `cube_groups/case_b_shapes.py` turns this into four exact SAT searches for t = 6
  (shapes c, d1, d2 with delta in P, d2 with delta + x0 in P). UNSAT for all four gives A(6) <= 7.
  The run is queued with its predictions written down first. The plain search of case-b.md, also
  queued, decides the same question without Proposition 27, so the two runs check each other.
- A census of every anisotropic system that U+ can carry at k = 3 (192 of them) confirms the case
  split of Proposition 27 at that level: 24 of shape c, 24 of shape d1, 144 of shape d2, none other.

## Setting

As in [case-b.md](case-b.md): X = F_2^t, sigma : V -> X quadratic with polar form beta, h -> A_h
linear with

    A_(h') sigma(h) = (I + A_h) beta(h, h')                                    (*)
    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').      (Q)

The system is anisotropic with dim V = t + k - 1, u has rank rho = t - k with 1 <= rho <= t - 2, and
A(s) = s for s <= k. We also assume 2 rho <= t, so that by Proposition 26 *every* element of rank rho
is in Case B (for k = 3 this means t <= 6; for k = 4, t <= 8). For an element w of rank rho write
x0(w) = sigma(w), X_1(w) = ker A_w, R(w) = Im A_w, N(w) = U+(w) = ker beta(w, .) (dimension k), and
drop (w) for w = u. Put P = beta(u, V), a hyperplane that misses x0, and Y = P n X_1.

Two consequences of (Q) are used throughout. For n in N and every h, with h_1 = u, h_2 = n, h' = h:

    A_n beta(u, h) = A_u beta(n, h),                                             (4)

and the same identity holds for any element w of rank rho and any m in N(w):
A_m beta(w, h) = A_w beta(m, h).

## Lemma 36 (a shared kernel)

**Lemma 36.** In the setting above, let n be in N with rank A_n = rho and A_n X_1 = 0. Then n is in
Case B with ker A_n = X_1 and Im A_n = R. If moreover beta(n, N) lies in span(sigma(n)), then
N(n) = N, and so beta(n, N) = 0.

*Proof.* n has rank rho, so it is in Case B (Proposition 26(c), (d) and 2 rho <= t). Its kernel
contains X_1 and has dimension k = dim X_1, so it is X_1; its image lies in R (Proposition 26(e)
for u) and has dimension rho = dim R, so it is R. Let m be in N(n). For n' in N, the identity
after (4), for the element n, gives A_n beta(m, n') = A_m beta(n, n'). Here beta(n, n') is a multiple
of sigma(n), and A_m sigma(n) = 0 by Proposition 26(e) for n. So beta(m, n') lies in ker A_n = X_1.
Also sigma(m) lies in X_1(n) = X_1 (Proposition 26(e) for n), and sigma(N) lies in X_1. Hence on
U' = N + span(m), sigma(n' + c m) = sigma(n') + c sigma(m) + c beta(n', m) lies in X_1. By Lemma 26(a)
U' carries an anisotropic system with values in X_1, so dim U' <= A(k) = k = dim N, and m lies in N.
So N(n) lies in N, and both have dimension k. QED

## Corollary 20 (shape (d2))

Recall shape (d2) of Proposition 27 (k = 3): N has a basis u, n_1, n_2 with sigma(n_1) = a,
sigma(n_2) = delta and beta(n_1, n_2) = delta, where x0, a, delta is a basis of X_1, A_(n_1) kills x0
and a and fixes delta, and A_(n_2) kills X_1.

**Corollary 20.** Let k = 3 (so 4 <= t <= 6 under 2 rho <= t) and let u be in shape (d2).
(a) A_(n_2) has rank at most rho - 1.
(b) If A_(u + n_2) has rank rho, then delta lies in P, and u + n_2 is again in shape (d2), with
    U+(u + n_2) = span(u, n_2, m) for some m with beta(u, m) = delta, and with the same n_2.
So if delta + x0 lies in P (instead of delta), then A_(n_2) and A_(u + n_2) both have rank <= rho - 1.

*Proof.* (a) A_(n_2) kills X_1 and has rank <= rho (Proposition 26(a)). beta(n_2, N) = span(delta)
lies in span(sigma(n_2)), and beta(n_2, n_1) = delta != 0. If the rank were rho, Lemma 36 would give
beta(n_2, N) = 0.

(b) Put w = u + n_2. A_w = A_u + A_(n_2) kills X_1; with rank rho it is in Case B with X_1(w) = X_1
and R(w) = R (as in Lemma 36), and sigma(w) = x0 + delta. beta(w, u) = 0, beta(w, n_2) = 0 and
beta(w, n_1) = delta != 0, so N(w) meets N in span(u, n_2), and N(w) = span(u, n_2, m) with m outside
N, that is beta(u, m) != 0. Write q = beta(u, m). By Proposition 26(e) for w, sigma(N(w)) lies in
X_1, so q = sigma(u + m) + sigma(u) + sigma(m) lies in X_1, hence in Y; and A_m (x0 + delta) = 0.
By (1) of case-b.md, A_m x0 = (I + A_u) q = q, so A_m delta = q. By (*) with h = n_2, h' = m,
A_m delta = (I + A_(n_2)) beta(n_2, m) = beta(n_2, m), because beta(n_2, m) lies in X_1 (n_2 and m are
in N(w)) and A_(n_2) kills X_1. So beta(n_2, m) = q.

Replacing n_1 by n_1 + u keeps the shape (it changes a to a + x0), so we may take a in Y; then
Y = span(a, delta + c x0) with c in {0, 1}. Write q = e a + f (delta + c x0). By (4), A_u beta(n_1, m) =
A_(n_1) q = f delta. If f = 0, then beta(n_1, m) lies in X_1, and with sigma(m), beta(u, m) and
beta(n_2, m) in X_1, all of sigma(N + span(m)) lies in X_1, against A(3) = 3 as in Lemma 36. So f = 1.

Now beta on N(w) = span(u, n_2, m) takes the values beta(u, n_2) = 0 and beta(u, m) = beta(n_2, m) = q,
so beta(N(w), N(w)) = span(q) != 0, and w is in shape (d1) or (d2). The elements of N(w) whose maps
kill X_1 are exactly those of K = span(u, n_2) = span(u, w): A_u and A_(n_2) kill X_1, and every
element with an m-component sends x0 to A_m x0 = q != 0. In shape (d1), with basis w, n_1', n_2' of
N(w), none of n_1', n_2', n_1' + n_2' kills X_1, nor does any of them plus w (A_w kills X_1); but K
has dimension 2 and contains w, so it contains one of them plus a multiple of w. So w is in shape
(d2), with basis w, n_1', n_2'. There n_2' kills X_1 and is not in span(w), so n_2' is u or n_2, and
beta(N(w), N(w)) = span(sigma(n_2')), so q = sigma(n_2') is x0 or delta. q lies in P and x0 does
not, so q = delta = sigma(n_2) and n_2' = n_2. Then e a + c x0 = 0, so e = c = 0, and delta lies in Y.
QED

Corollary 20 holds for t = 4, 5, 6. At t = 6 it says that in shape (d2) A_(n_2) has rank <= 2, and
that A_(u + n_2) has rank <= 2 too when delta + x0 lies in P. We have not found a contradiction in
any shape, so Case B at t = 6, and with it A(6) <= 7, is still open by hand.

## Lemma 37 (normal forms by shape)

**Lemma 37.** Let an anisotropic system with dim X = t and dim V = t + k - 1 have an element u of
rank t - k in Case B, with A(s) = s for s <= k. In the bases of Lemma 35 one can also take
v_1, ..., v_(k-1) in N and e_1, ..., e_(k-1) in Y so that (e_c are the basis vectors of X, e_0 = x0):

    shape c  (beta = 0 on N; always so for k = 2):  sigma(v_i) = e_i, beta(v_i, v_j) = 0 and
             A_(v_i) e_c = 0 for 1 <= i, j <= k - 1 and c < k;
    for k = 3 and beta != 0 on N, one of
    shape d1:  sigma(v_1) = e_1, sigma(v_2) = e_2, beta(v_1, v_2) = e_0, A_(v_1): e_0, e_1 -> 0,
               e_2 -> e_0, and A_(v_2): e_0, e_2 -> 0, e_1 -> e_0;
    shape d2c (c = 0 or 1), with delta = e_2 + c e_0: sigma(v_1) = e_1, sigma(v_2) = delta,
               beta(v_1, v_2) = delta, A_(v_1): e_0, e_1 -> 0, e_2 -> delta, and A_(v_2) e_c = 0
               for c <= 2.

*Proof.* Replacing an element n of N by n + u changes sigma(n) by x0 (beta(u, n) = 0), does not
change beta(n, n') for n' in N, and does not change A_n on X_1 (A_u kills X_1). X_1 = Y + span(x0).
Shape c: by Proposition 27(c1), sigma maps N linearly onto X_1 with sigma(u) = x0, so there are
v_1, ..., v_(k-1) in N with sigma(v_i) in Y forming a basis of Y; put e_i = sigma(v_i). The values
follow from beta = 0 on N and Proposition 27(c1). Shapes (d1) and (d2): take the basis u, n_1, n_2
of Proposition 27(d). In (d1), replace n_1 and n_2 by n_i + u where needed so that a and b lie in Y;
the equations of (d1) are kept (for example A_(n_1)(b + x0) = x0 because A_(n_1) x0 = 0), and
e_1 = a, e_2 = b. In (d2), replace n_1 by n_1 + u if needed so that a lies in Y (A_(n_1 + u) kills
x0 and a + x0 and fixes delta); exactly one of delta and delta + x0 lies in Y; call it e_2 = delta + c x0,
and e_1 = a. Then A_(n_1) e_2 = A_(n_1) delta = delta. In each case e_1, ..., e_(k-1) are independent
vectors of Y = P n ker A_u, so the proof of Lemma 35 can start from them, and from v_0 = u,
v_1, v_2 as the start of a basis of ker phi. QED

So Case B at (t, k) = (6, 3) exists if and only if one of the four forms c, d1, d2c0, d2c1 has a
model, and for k = 2 if and only if form c does.

## The census of systems on U+ (k = 3)

By Lemma 26(a), U+ = span(u, n_1, n_2) carries a system with values in X_1 = F_2^3, with the maps
A_h restricted to X_1 and projected onto it. In it sigma(u) = x0 = e_0, beta(u, U+) = 0 and A_u = 0,
and (*) with h = u forces A_(n_i) e_0 = 0. `case_b_shapes.n_census()` lists every anisotropic system
of this kind: it tries all A_1, A_2 in M_3(F_2) with A_i e_0 = 0 and A_i s_i = 0 (Lemma 21(b)), all
non-zero s_1, s_2 and all b = beta(n_1, n_2), 8 x (64 + 6 x 8)^2 = 100,352 tuples, and checks (*) by
brute force. It finds 192 systems: 24 with b = 0 (shape c, all maps 0), 24 with b = e_0 (shape d1)
and 144 with b outside span(e_0) (shape d2), and none of any other shape. The count by hand: each of
the 24 systems of Lemma 34 on U+/span(u) with values in X_1/span(e_0) has 8 lifts (two for each of
sigma(n_1), sigma(n_2) and b), and in each lift the maps are determined. This checks the case split
of Proposition 27(c1) and (d) for the projected maps; that the values hold for the maps themselves is
the hand proof.

## The exact search

`cube_groups/case_b_shapes.py` takes the CNF of [case_b.py](../cube_groups/case_b.py) (the normal
form of Lemma 35) and adds the values of Lemma 37 as unit clauses: 54 of them for each form at
(6, 3), 9 and 12 for form c at (3, 2) and (4, 2). The job (m12-shapes-v1, one CPU, queued on
2026-10-17) has pre-registered predictions: UNSAT for form c at (3, 2) and (4, 2) (A(3) = 3,
A(4) = 4); the four forms at (6, 3) are exploratory, and UNSAT for all four gives A(6) <= 7. In a
verified model at (6, 3), the hand results predict every rank <= 3 (Proposition 26(a)),
dim(X_1 n R) >= 2 in form c (Proposition 27(c4)), rank A_(v_2) <= 2 in forms d2c0 and d2c1
(Corollary 20(a)), and rank A_(v_0 + v_2) <= 2 in form d2c1 (Corollary 20(b)); the grader checks
these. The results will be added here.

## Computation

The unit tests of `cube_groups/case_b_shapes.py` (which gated this commit) check:

- the census above (100,352 tuples, 192 systems, 24 / 24 / 144 / 0);
- that the values of the four forms, read on U+ and X_1, are systems of shapes c, d1, d2 and d2;
- that each form adds exactly the stated number of unit clauses, on distinct variables, to the CNF
  of case_b.py, that these clauses accept coordinates carrying the form's values, and that changing
  one fixed bit leaves the form.

## Prior work

As for the earlier notes: searches on 2026-10-15 to 2026-10-17 found nothing on the identity (*), on
A(t) or on Question R. A search on 2026-10-17 found no classification of spaces of matrices of rank
at most 3 over F_2 (de Seguins Pazzis, arXiv 1405.1575, completes rank at most 2 over F_2, which
Lemma 29 uses). The tools are elementary, so a specialist may know them. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
