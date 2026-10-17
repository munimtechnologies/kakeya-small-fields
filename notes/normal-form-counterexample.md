# The normal-form conjecture of finite-groups.md 1.7.5 is false

By MV2 of Munim, Inc., 2026-10-17. A correction to section 14 of finite-groups.md (version 1.7.5),
to be merged into that file in version 1.7.6. Researched and written with AI agents working in
MV2's name. The example below was checked by hand and is checked exactly by
`cube_groups/nf_pencil.py` and its unit tests (this note was committed only after they passed). **No
human mathematician has checked it.** Text CC BY 4.0, code Apache-2.0.

## What changes

Version 1.7.5 conjectured, after Lemma 23, that every *system* (a quadratic map sigma : V -> X = F_2^t
with polar form beta, and a linear map h -> A_h from V to End(X), satisfying

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V          (*)

) has the normal form sigma(h) = (I + A_h) lam(h) with lam : V -> X linear. **That is false**: below
is a system with t = 3 and dim V = 2 that has no normal form. Lemma 23 (a)-(d), Proposition 20 and
everything else in section 14 are unaffected. In particular the question that decides the
Z_4^a x Z_2^b family, whether M(t) <= t + 1 for every t (and M(3) <= 5 for the open cases (6, 2) and
(5, 3)), is still open. The counterexample needs only codimension 2 < t, so it does not bear on
M(t) = t; it only shows that the normal form cannot be the route to it.

## A criterion (draft Lemma 24)

Let alpha be one-to-one, with basis e_1, ..., e_r of V, A_i = A_(e_i), q_i = sigma(e_i),
b_ij = beta(e_i, e_j), and Fix(A) = ker(I + A).

(a) (*) holds if and only if A_j q_i = (I + A_i) b_ij for all i, j (with b_ii = 0) and
A_k b_ij + A_i b_jk + A_j b_ik = 0 for all distinct i, j, k.

(b) sigma has the normal form if and only if there are f_i in Fix(A_i) with

    f_i + f_j + b_ij  in  Fix(A_i + A_j)     for all i < j.

(c) For a pencil (r = 2, b = b_12): the normal form holds if and only if
b lies in Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2). It holds when one of A_1, A_2, A_1 + A_2 is
invertible, and it holds for every pencil when t = 2.

*Proof.* (a) Both sides of (*) are linear in h', so take h' = e_k. Then
Q_k(h) = A_k sigma(h) + (I + A_h) beta(h, e_k) is a quadratic map with Q_k(0) = 0, so it vanishes iff
it vanishes at each e_i and its polar form vanishes at each pair e_i, e_j. The first gives
A_k q_i = (I + A_i) b_ik; the polar form of h -> A_h beta(h, e_k) at (e_i, e_j) is
A_i b_jk + A_j b_ik, and that of h -> A_k sigma(h) is A_k b_ij. For k in {i, j} the polar condition
is empty.
(b) By (a), A_i q_i = 0, so (I + A_i) q_i = q_i and the solutions of (I + A_i) lam_i = q_i are
lam_i = q_i + f_i with f_i in Fix(A_i). The quadratic maps sigma and h -> (I + A_h) lam(h) agree at
each e_i; their polar forms at (e_i, e_j) are b_ij and A_i lam_j + A_j lam_i. By (a),
A_j q_i + A_i q_j = (A_i + A_j) b_ij, and with A_i f_i = f_i one checks
A_j f_i + A_i f_j = (I + A_i + A_j)(f_i + f_j). So the polar forms agree iff
(I + A_i + A_j)(f_i + f_j) = (I + A_i + A_j) b_ij, which is the displayed condition.
(c) The first sentence is (b) for r = 2. If A_1 is invertible, then q_1 = 0 and (a) gives
(I + A_1) b = A_2 q_1 = 0, so b is in Fix(A_1); A_2 is the same, and for A_1 + A_2 use the basis
e_1, e_1 + e_2, for which beta is still b. For t = 2, suppose no element of the pencil is invertible.
The non-zero singular 2 x 2 matrices have rank 1 and are nilpotent (Fix = 0) or idempotent (Fix =
their image, a line). No pencil in M_2(F_2) is nilpotent throughout (the three non-zero nilpotents
add to invertible matrices), so if the three Fix spaces do not span X, they all lie in one line l and
some element of the pencil is idempotent with image l; change the basis of the pencil so that this
element is A_1. In a basis
(u, w) of X with A_1 = E_11, l = span(u), (a) gives q_1 = x w and A_2 q_1 = (I + A_1) b = b_2 w,
where b = b_1 u + b_2 w. If x = 0 or b_2 = 0, b is in l. Otherwise A_2 w = w, so A_2 = [[a, 0], [c, 1]],
and singular means a = 0; then Fix(A_2) = span(w) is not in l, a contradiction. QED

## The counterexample

t = 3, V = F_2^2, with (1-based matrix entries)

    A_1 = E_11,   A_2 = E_12 + E_13 + E_21 + E_22,   A_1 + A_2 = E_11 + E_12 + E_13 + E_21 + E_22,
    sigma(e_1) = e_2 + e_3,   sigma(e_2) = e_1 + e_2 + e_3,   beta(e_1, e_2) = e_2,

so sigma(e_1 + e_2) = e_1 + e_2. Criterion (a): A_1 q_1 = 0, A_2 q_2 = 0,
A_2 q_1 = e_2 = (I + A_1) e_2, and A_1 q_2 = e_1 = (I + A_2) e_2, so (*) holds (all 16 pairs (h, h')
are also checked one by one). Fix(A_1) = span(e_1), and A_2 and A_1 + A_2 have no non-zero fixed
vector, so Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2) = span(e_1) does not contain b = e_2, and by (c)
there is no normal form. Directly: lam(e_1) is e_2 + e_3 or e_1 + e_2 + e_3, lam(e_2) must be
e_1 + e_2 + e_3, and then (I + A_1 + A_2) lam(e_1 + e_2) is 0 or e_2, never sigma(e_1 + e_2) = e_1 + e_2.

Three more facts, all checked by the code. All three non-zero A_h are singular (they must be, by (c)).
sigma vanishes only at 0, so the system is *anisotropic* and its least codimension is 2. And the
solution space of (*) for this pencil is 1-dimensional and stays 1-dimensional when y = 1, 2, 3
kernel directions are added (Lemma 21's reduced systems): a kernel vector k must have
A_c (I + A_c) sigma(k) = 0 for every c, which here forces sigma(k) = 0.

## What is being computed next

`cube_groups/nf_pencil.py` (queued 2026-10-17 with pre-registered predictions): (1) every pencil
in M_2(F_2) (35) and M_3(F_2) (43,435), and 3,000 random pencils in M_4(F_2): how many fail the
criterion, with brute force agreeing with (c) on every failing system and thousands of passing
ones, and no failing pencil containing an invertible matrix; (2) draft Lemma 24(b) against brute
force for every 3-dimensional C in M_2(F_2) and 400 random ones in M_3(F_2); (3) *anisotropic*
systems (sigma(h) != 0 for all h != 0). An anisotropic system has least codimension dim V, every
A_h with h outside ker alpha is singular, and restrictions stay anisotropic. So one with t = 3 and
dim V = 4 would give M(3) >= 4 > t, and if there is none, no anisotropic system with t = 3 has
dim V >= 4. The search lists every subspace of M_3(F_2) whose non-zero elements are all singular.
Controls: t = 1 and t = 2 have none with dim V = t + 1 (as M(1) = 1, M(2) = 2 require).

Please open an issue at https://github.com/munimtechnologies/kakeya-small-fields if you see an
error, or if this is known.
