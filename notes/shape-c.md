# Shape (c) of Case B: commuting matrices, an invariant plane, and a finer split

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10, next to
[case-b-shapes.md](case-b-shapes.md) and [case-b.md](case-b.md). Numbering continues from
case-b-shapes.md (Lemma 38, Lemma 39, Corollary 21). This is partial progress: it settles no new case
of Corollary 17. It was researched and written with AI agents working in MV2's name. The proofs are
by hand; `cube_groups/shape_c.py` counts the commuting pairs of 3 x 3 matrices over F_2 and their
orbits, checked against hand counts, and its unit tests gated this commit. No human mathematician has
checked the proofs. Text CC BY 4.0, code Apache-2.0.

## What changes

- **Lemma 38.** In shape (c) (beta vanishes on U+), every element n of U+ gives a matrix M_n on
  X / ker A_u with A_n = T M_n T^(-1) A_u, where T is the isomorphism that A_u induces. These matrices
  **commute**, M_u = I, and every n with M_n invertible is again a Case B element with the same
  kernel, image, U+ and W. A quadratic identity ties the M_n to the values of sigma on W.
- **Corollary 21.** At t = 6 (k = 3, rank 3), in shape (c) either A_u^2 = 0, or the matrices M_n have
  a common invariant plane, spanned by the values of sigma on W modulo ker A_u.
- **Lemma 39** shows which changes of basis keep the normal form of shape (c), and they act on the
  pair (M_(v_1), M_(v_2)) by simultaneous conjugation and by recombination. So shape (c) at t = 6 splits
  into one exact search per orbit of commuting pairs of 3 x 3 matrices over F_2 under
  GL_3(F_2) x GL_2(F_2). There are 7,456 commuting pairs; `cube_groups/shape_c.py` computes the
  orbits and their representatives.
- The split search (job m13) is written and tested but **not run**. It is meant for the case that
  m12 (case-b-shapes.md), which is still waiting for compute, leaves shape (c) at t = 6 undecided.

## Setting

As in [case-b-shapes.md](case-b-shapes.md): X = F_2^t, sigma : V -> X quadratic with polar form beta,
h -> A_h linear with

    A_(h') sigma(h) = (I + A_h) beta(h, h')                                    (*)
    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').      (Q)

The system is anisotropic with dim V = t + k - 1, u has rank rho = t - k with 1 <= rho <= t - 2,
A(s) = s for s <= k, and 2 rho <= t. Put x0 = sigma(u), phi = beta(u, .), X_1 = ker A_u (dimension k),
R = Im A_u (dimension rho), N = U+ = ker phi (dimension k), P = phi(V), a hyperplane missing x0,
Y = P n X_1 (dimension k - 1) and W = phi^(-1)(Y) (dimension 2k - 1). We assume **shape (c)**: beta
vanishes on N x N. Then (Proposition 27(c)) sigma maps N linearly onto X_1, A_n kills X_1 and has image
in R for n in N, and for h in W, beta(h, N) lies in X_1 and A_h maps X_1 into itself.

Write [x] for the class of x in X/X_1. As A_u has kernel X_1 and image R, it induces an isomorphism
T : X/X_1 -> R, T[x] = A_u x. Since x0 lies in X_1 but not in P, P + X_1 = X, so [P] = X/X_1.

## Lemma 38 (the matrices of U+)

For n in N, A_n kills X_1 and has image in R, so A_n x = T M_n [x] for one linear map M_n of X/X_1;
equivalently A_n = T M_n T^(-1) A_u.

**Lemma 38.** In the setting above:

(a) n -> M_n is linear, M_u = I, rank A_n = rank M_n, and [beta(n, h)] = M_n [phi(h)] for all h in V.

(b) The M_n (n in N) commute with each other.

(c) If M_n is invertible, then n is in Case B with ker A_n = X_1, Im A_n = R and U+(n) = N, and
    beta(n, h) lies in X_1 exactly when h lies in W. So W is the same for n as for u, and beta(n, .)
    maps W onto a complement of span(sigma(n)) in X_1, with kernel N.

(d) For y in Y pick h_y in W with phi(h_y) = y, and let G_y be A_(h_y) restricted to X_1. Then G_y
    does not depend on the choice, G_y sigma(n) = beta(n, h_y) for n in N, G_y x0 = y,
    q(y) = [sigma(h_y)] does not depend on the choice either, and

        (G_y + G_y^2) sigma(n) = T M_n q(y)          for all n in N and y in Y.          (5)

(e) Let D = T^(-1)(X_1 n R), of dimension d = dim(X_1 n R). Then M_n q(y) lies in D for all n in N
    and y in Y, q(y) != 0 for y != 0, and the q(y) span a subspace of D of dimension at least k - 1.

*Proof.* (a) Linearity is clear, and M_u = T^(-1) T = I. As T is an isomorphism, A_n and M_n have the
same rank. (Q) with h_1 = u, h_2 = n, h' = h gives (4) of case-b-shapes.md,
A_n phi(h) = A_u beta(n, h); the left side is T M_n [phi(h)] and the right side is T [beta(n, h)].

(b) (Q) with h_1 = n, h_2 = n', h' = h and beta(n, n') = 0 gives A_n beta(n', h) = A_(n') beta(n, h).
By (a) the left side is T M_n [beta(n', h)] = T M_n M_(n') [phi(h)], and the right side is
T M_(n') M_n [phi(h)]. The classes [phi(h)] fill X/X_1 and T is one-to-one, so M_n M_(n') = M_(n') M_n.

(c) A_n has rank rho = rank M_n and kills X_1, so by Lemma 36 (with beta(n, N) = 0) n is in Case B
with ker A_n = X_1, Im A_n = R and U+(n) = N. By (a), [beta(n, h)] = 0 iff M_n [phi(h)] = 0 iff
[phi(h)] = 0 iff phi(h) lies in X_1 n P = Y, that is, h lies in W. In Case B, P_n = beta(n, V) is a
hyperplane missing sigma(n), which lies in X_1; so P_n n X_1 = beta(n, W) is a complement of
span(sigma(n)) in X_1, of dimension k - 1 = dim W - dim N, and the kernel of beta(n, .) on W is
U+(n) = N.

(d) Two choices of h_y differ by an element of N, whose map kills X_1, and whose sigma value and beta
values with W lie in X_1; so G_y and q(y) do not depend on the choice. (*) with h = n, h' = h_y gives
A_(h_y) sigma(n) = (I + A_n) beta(n, h_y) = beta(n, h_y), as beta(n, h_y) lies in X_1, which A_n
kills; for n = u this is G_y x0 = phi(h_y) = y. (*) with h = h_y, h' = n gives
A_n sigma(h_y) = (I + A_(h_y)) beta(h_y, n) = (G_y + G_y^2) sigma(n), and the left side is
T M_n [sigma(h_y)].

(e) The left side of (5) lies in X_1 (G_y maps X_1 into itself) and the right side lies in R, so
T M_n q(y) lies in X_1 n R. q(y) != 0 for y != 0 by Proposition 27(c3) (h_y is in W but not in N).
For the last claim: in the proof of Proposition 27(c4), W carries, modulo X_1, an anisotropic system
on W/N (dimension k - 1) with values in span [sigma(W)] = span q(Y); as A(s) = s for s <= k - 1, this
span has dimension at least k - 1. QED

**Corollary 21.** Let t = 6, k = 3 (rank 3) and let u be in shape (c). Then either R = X_1, so that
A_u^2 = 0, or D is a plane that is invariant under every M_n (n in N) and is spanned by the q(y).

*Proof.* By Proposition 27(c4), d >= 2, and d <= dim R = 3. If d = 3, then X_1 n R = R, and R and X_1
both have dimension 3, so R = X_1. If d = 2, then by Lemma 38(e) the q(y) span a subspace of D of
dimension at least 2, so they span D, and M_n D lies in D for every n. QED

So in shape (c) at t = 6, the commuting space {M_n} contains I, and if it has no common invariant
plane, then A_u^2 = 0.

## Lemma 39 (symmetries of the normal form of shape (c))

In the bases of Lemma 35 and the values of Lemma 37 (shape (c)), X_1 = span(e_0, ..., e_(k-1)), so
[e_k], ..., [e_(t-1)] is a basis of X/X_1. Write M_i for the matrix of M_(v_i) in this basis (column j
is the image of [e_(k+j)]). Then Lemma 38(a) says, column by column,

    A_(v_i) e_(k+j) = A_u (sum over l of M_i[l][j] e_(k+l))       (0 <= j < t - k).      (S)

**Lemma 39.** If some anisotropic system has an element u in Case B with shape (c), then for every
g in GL_(t-k)(F_2) and every invertible (k - 1) x (k - 1) matrix c = (c_ab), it has one in the normal
form of Lemmas 35 and 37 (shape (c)) whose matrices are M'_a = g^(-1) (sum over b of c_ab M_b) g.

*Proof.* Start from the normal form with matrices M_i. Replace v_1, ..., v_(k-1) by
v'_a = sum_b c_ab v_b; they lie in N, beta vanishes on them and on u, their maps kill X_1, and
sigma(v'_a) = sum_b c_ab e_b (sigma is linear on N) is again a basis of Y. Take e'_a = sigma(v'_a) for
1 <= a <= k - 1, replace v_k, ..., v_(2k-2) (phi(v_(k-1+j)) = e_j) by the same combinations so that
phi(v'_(k-1+a)) = e'_a, and keep the rest. This is again the normal form of shape (c), and
M_(v'_a) = sum_b c_ab M_b by Lemma 38(a). Next put e'_(k+j) = sum_l g[l][j] e_(k+l) for 0 <= j < t - k,
and replace v_(2k-1+j) (phi = e_(k+j)) by the same combinations of them. These e' lie in P and span a
complement of X_1, and the conditions of Lemma 35 (sigma(u), phi on the basis of V, A_u e_c = 0 for
c < k) still hold. In the new basis of X/X_1 every M_n has the matrix g^(-1) M_n g. QED

So the pair (or tuple) (M_1, ..., M_(k-1)) of a shape (c) element can be moved to a fixed
representative of its orbit under GL_(t-k) (simultaneous conjugation) x GL_(k-1) (recombination),
and by Lemma 38(b) the M_i commute. For t = 6, k = 3 these are pairs of commuting 3 x 3 matrices over
F_2. There are 7,456 of them: summing 2^(dim of the centraliser) over the 14 similarity classes of
M_3(F_2) gives

    2 x 512 + 2 x 21 x 32 + 2 x 42 x 8 + 2 x (28 x 32 + 84 x 8) + 2 x 24 x 8 + 2 x 56 x 8 = 7,456

(the classes 0 and I; rank-1 nilpotent and its shift by I; regular nilpotent and its shift; the
split classes with characteristic polynomial x^2 (x + 1) or x (x + 1)^2; the two irreducible cubics;
(x + 1)(x^2 + x + 1) and x (x^2 + x + 1)), which agrees with the Feit-Fine generating function
(168 x 932/21). The group GL_3(F_2) x GL_2(F_2) has order 1,008. Fourteen orbits consist of pairs
spanning at most a line ((0, 0), and one orbit for each of the 13 non-zero similarity classes); the
others correspond to the similarity classes of 2-dimensional commutative subspaces of M_3(F_2), each
with all of its ordered bases.

## The split search (prepared, not run)

`cube_groups/shape_c.py` takes the CNF of case_b_shapes.py for shape (c) and adds the parity equations
(S) for one representative (M_1, ..., M_(k-1)) of each orbit (the least pair of the orbit). For
t - k <= 3 each equation has at most four variables, so no variables are added. Shape (c) at (t, k)
exists if and only if one of these CNFs is satisfiable (Lemmas 37, 38(b), 39). Each instance fixes
the pair (M_(v_1), M_(v_2)), which the plain shape (c) search had to find together with everything
else; whether that makes the instances easy enough for one CPU is what a run would show.

A run is planned only if m12 leaves shape (c) at t = 6 undecided, with predictions written down
first: UNSAT for every orbit at (t, k) = (3, 2) (2 orbits) and (4, 2) (6 orbits), since
A(3) = 3 and A(4) = 4. In a verified model the grader checks Proposition 26(a) and Lemma 38: M_u = I,
the M_n commute, (5) holds, and M_n q(y) lies in D.

## Computation

The unit tests of `cube_groups/shape_c.py` (which gated this commit) check:

- the numbers of commuting tuples: 2, 16, 88 and 7,456 for single 1 x 1 and 2 x 2 matrices, pairs
  of 2 x 2 and pairs of 3 x 3 matrices; the numbers of orbits 2, 6, 14 for single 1 x 1, 2 x 2 and
  3 x 3 matrices (the similarity classes) and 9 for pairs of 2 x 2 matrices (orbit sizes
  1, 3, 6, 6, 9, 9, 18, 18, 18, counted by hand);
- for pairs of 3 x 3 matrices, that the orbit sizes add up to 7,456, that orbit size times stabiliser
  size is 1,008 for each orbit, that exactly 1 + 13 orbits span at most a line, and that the action
  composes as a group action;
- that the parity equations add exactly the predicted clauses and no variables, that coordinates
  built to satisfy (S) are accepted and give back M_u = I and M_(v_i) = M_i, and that changing one
  bit of a column of A_(v_i) is rejected.

## Prior work

Commuting pairs of matrices over finite fields are classical (Feit and Fine, 1960, count them). As for
the earlier notes, searches on 2026-10-15 to 2026-10-17 found nothing on the identity (*), on A(t) or
on Question R, so the use of the commuting matrices M_n here appears to be new; the tools are
elementary, so a specialist may know them. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
