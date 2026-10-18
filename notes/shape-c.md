# Shape (c) of Case B: commuting matrices, an invariant plane, and a finer split

MV2 of Munim, Inc., 2026-10-17 and 2026-10-18. Added to kakeya-small-fields after version 1.7.10,
next to [case-b-shapes.md](case-b-shapes.md) and [case-b.md](case-b.md). Numbering continues from
case-b-shapes.md (Lemma 38, Lemma 39, Corollary 21, Lemma 40, Lemma 41, then Lemma 46 and Corollary
23, added on 2026-10-18 after Corollary 22 of case-b-shapes.md). It settles no case of Corollary 17
by itself; with the run of job m13 and Lemma 47 of [case-a.md](case-a.md) it rules out Case B at
t = 5 and rank 3 (Corollary 24 there). It was researched and written with AI agents working in MV2's
name. The proofs are by hand; `cube_groups/shape_c.py` counts the commuting pairs of 3 x 3 matrices
over F_2 and their orbits, checked against hand counts, and its unit tests gated the commit that
added it. Lemma 40 was added later by hand, with no computer check yet. Lemma 41 and
`cube_groups/shape_c2.py` were added after that; the unit tests of shape_c2.py check the counts of
Lemma 41 against hand counts. Lemma 46 and Corollary 23 are hand proofs with no computer check. No
human mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

Since Corollary 22 of [case-b-shapes.md](case-b-shapes.md) (2026-10-18), shape (c) is the only shape
left at (t, k) = (6, 3): A(6) <= 7 holds if and only if no anisotropic system with t = 6 and
dim V = 8 has an element of rank 3 in Case B in shape (c).

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
- **Lemma 40** (by hand). When U+ has dimension 2, the map G on ker A_u that comes from W has one
  of three forms (G^2 = 0, G^2 = I, or G^2 + G + I = 0), and each form fixes how the single matrix M
  of U+ acts on the value q of sigma on W. If neither M nor M + I is singular, then ker A_u lies in
  Im A_u.
- **Lemma 41** (by hand). When U+ has dimension 2, the vector M q alone decides which form of
  Lemma 40 holds, and a Case B element can be moved to a normal form in which M, q, the value of sigma
  on W and several more values are fixed. Case B at t = 5, rank 3, then splits into 47 exact searches
  instead of 14. `cube_groups/shape_c2.py` builds them; they are no longer needed at t = 5 (see below).
- **Lemma 46** (by hand). An element h_y of W acts on X / ker A_u like the matrix M of the element of
  U+ with the same value y, up to a map into the small subspace [Im A_u]. Since every map A_h kills
  sigma(h), this gives **(G_y + G_y^2) y in Im A_u^2 n ker A_u** for every y in Y.
- **Corollary 23** (by hand). At t = 6, unless A_u is nilpotent with Jordan blocks of sizes 3, 2
  and 1, the three matrices M_n with sigma(n) in Y \ {0} are all singular, and so is every G_y with
  y != 0. In every case the M_n have a common invariant plane, so the 5 orbits of commuting pairs
  whose matrices generate a copy of the field F_8 contain no model. At t = 5 the lemma adds linear
  conditions on Im A_u^2 to cases (ii) and (iii) of Lemma 40.
- **The split search of Lemma 39 ran** (job m13-shapec-v1, 2026-10-17 23:39 to 2026-10-18 01:55 UTC).
  Every graded prediction held. At t = 5 (k = 2, where shape (c) is all of Case B) it refuted 12 of
  the 14 instances; the other two (M = 0 and M = I) are ruled out by hand in Lemma 47 of
  [case-a.md](case-a.md), so **Case B does not occur at t = 5 and rank 3** (Corollary 24 there). At
  (6, 3) every instance it reached (30 of 38) hit its 4-minute limit, so A(6) <= 7 is still open.

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

The assumption 2 rho <= t is used only in Lemma 38(c) (through Lemma 36). Lemma 38(a), (b), (d),
(e), Lemma 39, Lemma 40, Lemma 41 and Lemma 46 hold for every u in Case B with beta = 0 on N, without
it; in particular for t = 5 and rank 3 (k = 2), where 2 rho = 6 > t.

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
plane, then A_u^2 = 0. Corollary 23 below shows that it always has one.

## Lemma 40 (U+ of dimension 2)

For k = 2, beta vanishes on N automatically (Proposition 27(c)), so every Case B element is in shape
(c). Write N = span(u, v), e_1 = sigma(v), so that Y = span(e_1) and X_1 = span(x0, e_1), and put
M = M_v, G = G_(e_1) and q = q(e_1) (Lemma 38(d)).

**Lemma 40.** In this situation G x0 = e_1, and G e_1 = beta(v, w) = a x0 + b e_1 (w in W with
phi(w) = e_1) for one of:

(i) (a, b) = (0, 0): G^2 = 0, T q = e_1 and M q = 0, so M is singular;
(ii) (a, b) = (1, 0): G^2 = I, T q = x0 + e_1 and M q = q, so M + I is singular;
(iii) (a, b) = (1, 1): G^2 + G + I = 0, T q = x0 and T M q = e_1, so X_1 lies in R.

In particular, if M and M + I are both invertible (no eigenvalue in F_2; for t = 5 this means the
characteristic polynomial of M is one of the two irreducible cubics), then (iii) holds and
X_1 = ker A_u lies in R = Im A_u.

*Proof.* G x0 = e_1 and G e_1 = beta(v, w) are Lemma 38(d), and G maps X_1 into itself, so
G e_1 = a x0 + b e_1 for some a, b. Then G^2 x0 = a x0 + b e_1 and G^2 e_1 = a e_1 + b(a x0 + b e_1) =
ab x0 + (a + b) e_1, so

    (G + G^2) x0 = a x0 + (1 + b) e_1,      (G + G^2) e_1 = a(1 + b) x0 + a e_1.

By (5) with n = u (sigma(u) = x0, M_u = I) and with n = v (sigma(v) = e_1), these are T q and T M q.
As q != 0 (Lemma 38(e)) and T is one-to-one, T q != 0, which rules out (a, b) = (0, 1). For (0, 0):
T q = e_1 and T M q = 0, so M q = 0 with q != 0, and G e_1 = 0 gives G^2 = 0. For (1, 0): T q =
x0 + e_1 = T M q, so M q = q, and G swaps x0 and e_1. For (1, 1): T q = x0 and T M q = e_1, so x0 and
e_1 lie in Im T = R; and G^2 x0 + G x0 + x0 = (x0 + e_1) + e_1 + x0 = 0, likewise on e_1. If M is
invertible, (i) is impossible; if M + I is invertible, (ii) is impossible. QED

The proof uses only Lemma 38(a), (d) and (e), so it holds without 2 rho <= t. It agrees with Lemma
38(c) where that applies: if M is invertible, then beta(v, W) = span(G e_1) must miss span(e_1), so
a = 1. Lemma 40 is not used in the split search of job m13, so a run of that search does not depend on
it. The finer split of Lemma 41 below does use it.

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

For k = 2 there is a single matrix M_1 and no recombination, so the orbits are the similarity classes
of M_(t-2)(F_2): 14 of them at t = 5.

## Lemma 41 (a finer normal form when U+ has dimension 2)

Let k = 2 and use the normal form of Lemmas 35, 37 and 39: u = v_0, v = v_1 with sigma(v) = e_1,
w = v_2 with phi(w) = e_1, x0 = e_0, X_1 = span(e_0, e_1), and M = M_v in the basis [e_2], ...,
[e_(t-1)] of X/X_1. Put q = [sigma(w)], and identify q with its coordinates in that basis.

**Lemma 41.** (a) The three cases of Lemma 40 are told apart by M q: case (i) holds iff M q = 0,
case (ii) iff M q = q, and case (iii) iff M q is neither 0 nor q.

(b) If some anisotropic system with dim X = t and dim V = t + 1 has a Case B element of rank t - 2,
then it has one in this normal form where M is any chosen matrix of its similarity class, q is any
chosen vector of its orbit under the centraliser C(M) of M in GL_(t-2)(F_2), and

    case   beta(v, w)    sigma(w) - (q on e_2, ..., e_(t-1))    A_w e_0, A_w e_1    T q         also
    (i)    0             0                                      e_1, 0              e_1
    (ii)   x0            0 or x0                                e_1, x0             x0 + e_1
    (iii)  x0 + e_1      0                                      e_1, x0 + e_1       x0          T M q = e_1

*Proof.* (a) Each case of Lemma 40 implies the condition on M q in its row (in (iii), T q = x0 and
T M q = e_1 are independent, so M q is neither 0 nor q, as T is one-to-one), and exactly one case
holds. The conditions exclude each other, so M q decides the case.

(b) By Lemma 39 (with k = 2 there is no recombination) we may take M to be the chosen matrix of its
class. For g in C(M), Lemma 39 with this g keeps M (g^(-1) M g = M) and keeps w, and the new
coordinates of sigma(w) modulo X_1 are g^(-1) q; so q can be moved anywhere in its C(M)-orbit. The
case is the same for g^(-1) q by (a), as M g^(-1) q = g^(-1) M q. beta(v, w) = G e_1 = a x0 + b e_1 with
(a, b) as in Lemma 40, and A_w e_0 = G x0 = e_1, A_w e_1 = G e_1 (Lemma 38(d)); T q and T M q are
Lemma 40. Finally, replace w by w + n for n in N. This keeps phi(w) = e_1, beta(v, w) (beta vanishes
on N), A_w on X_1 (A_n kills X_1) and q (sigma(n) and beta(w, n) lie in X_1), so the normal form is
kept, and it adds sigma(n) + beta(w, n) to sigma(w): x0 + e_1 for n = u and e_1 + beta(v, w) for n = v.
These span X_1 in cases (i) (e_1) and (iii) (x0), so the part of sigma(w) in X_1 can be made 0; in
case (ii) both are x0 + e_1, so that part can be made 0 or x0. QED

Counting the orbits of C(M) on the non-zero vectors of F_2^(t-2), class by class, gives 2, 10 and
38 pairs (M, q) for t = 3, 4 and 5; case (ii) has two choices for sigma(w), so there are 3, 13 and 47
instances. For t = 5 (m = 3), with the module structure of F_2^3 under M: the classes 0, I and the
two irreducible cubics have one orbit each (C(M) is GL_3(F_2) or the multiplicative group of F_8,
transitive); the rank-1 nilpotent, the regular nilpotent and their shifts by I have three (by height);
the diagonalisable split classes have three, the non-diagonalisable ones five; and
(x + 1)(x^2 + x + 1) and x (x^2 + x + 1) have three. Of the 38 pairs, 9 are in case (i), 9 in case (ii)
and 20 in case (iii). The centralisers have orders 168, 168, 8, 8, 4, 4, 6, 6, 2, 2, 7, 7, 3 and 3
(168 divided by the class sizes of the sum above).

Lemma 41 is a normal form, not a contradiction. In case (iii), X_1 lies in R, so A_u^2 has rank 1 and
X_2 = ker A_u^2 is a hyperplane; the 5-dimensional subspace U = {h : [phi(h)] in span(q, M q)} would
give a contradiction with A(4) = 4 (Lemma 26(a)) if sigma(U) lay in X_2, but we have not shown that.
Lemma 46 below adds that in case (iii) the image of A_u^2 is exactly span(e_1).

## Lemma 46 (an element of W on X / X_1)

For y in Y let n_y be the element of N with sigma(n_y) = y (sigma maps N one-to-one onto X_1). In the
normal form, n_y runs over N_Y = sigma^(-1)(Y) = span(v_1, ..., v_(k-1)). As A_(h_y) maps X_1 into
itself, it induces a linear map Abar_y of X/X_1. Put

    L = [R] = (R + X_1)/X_1,  a subspace of X/X_1 of dimension rho - d,

so that T(L) = A_u(R) = Im A_u^2 and T(L n D) = Im A_u^2 n X_1 (T maps L onto Im A_u^2 and D onto
X_1 n R, and Im A_u^2 lies in R).

**Lemma 46.** In the setting above (shape (c); 2 rho <= t is not needed), for every y in Y:

(a) Abar_y xi + M_(n_y) xi lies in L for every xi in X/X_1;

(b) T q(y) = y + G_y y;

(c) M_(n_y) q(y) lies in L n D. Equivalently,

        G_y T q(y) = (G_y + G_y^2) y   lies in   Im A_u^2 n ker A_u.

*Proof.* (a) (*) with h -> n_y and h' -> h gives A_h y = (I + A_(n_y)) beta(n_y, h). (Q) with
h_1 = u, h_2 = h and h' = h_y gives A_(h_y) phi(h) = A_u beta(h, h_y) + A_h y. Together

    A_(h_y) phi(h) = beta(n_y, h) + A_(n_y) beta(n_y, h) + A_u beta(h, h_y).

The last two terms lie in R (the image of every A_n with n in N lies in R), so their classes lie in
L, and [beta(n_y, h)] = M_(n_y) [phi(h)] by Lemma 38(a). The classes [phi(h)] fill X/X_1.

(b) (5) with n = u reads T q(y) = (G_y + G_y^2) x0 = y + G_y y, as G_y x0 = y.

(c) In every system, (*) with h' = h gives A_h sigma(h) = (I + A_h) beta(h, h) = 0. With h = h_y,
whose value has class q(y), this says Abar_y q(y) = 0, so M_(n_y) q(y) lies in L by (a). By (5) with
n = n_y, T M_(n_y) q(y) = (G_y + G_y^2) y, which lies in X_1, so M_(n_y) q(y) also lies in D. Applying
T gives the second form, and (G_y + G_y^2) y = G_y (y + G_y y) = G_y T q(y) by (b). QED

The new input is A_(h_y) sigma(h_y) = 0, used at an element of W, not of U+. For k = 2 the
second form of (c) gives, in the cases of Lemma 40 ((G + G^2) e_1 is 0, x0 + e_1 and e_1 there):

- case (i): nothing new;
- case (ii): x0 + e_1 = T q lies in Im A_u^2; equivalently, some vector of R = Im A_u has class q;
- case (iii): e_1 lies in Im A_u^2. There X_1 lies in R, so Im A_u^2 = A_u(R) has dimension
  rho - 2 = 1 at t = 5, hence **Im A_u^2 = span(e_1), A_u^3 = 0 and L = span(M q)**.

These are extra conditions for the 47 instances of Lemma 41. shape_c2.py does not use them.

## Corollary 23 (t = 6: singular matrices and a common invariant plane)

**Corollary 23.** Let t = 6, k = 3, dim V = 8 and let u be in shape (c).

(a) Unless A_u is nilpotent with Jordan blocks of sizes 3, 2 and 1 (rank A_u^2 = 1 and A_u^3 = 0),
    M_(n_y) q(y) = 0 and G_y T q(y) = 0 for every y in Y. Then the three matrices M_n with n in
    N_Y \ {0} are singular, and every G_y with y != 0 is singular.

(b) In the situation of (a), for each y != 0 put z = G_y y. Either z = 0 (then T q(y) = y), or
    x0, y, z is a basis of X_1 with G_y: x0 -> y, y -> z, z -> z (then G_y has rank 2, T q(y) = y + z,
    and q(y) spans a line that is invariant under every M_n).

(c) If A_u^2 = 0, then Abar_y = M_(n_y), and rank G_y + rank M_(n_y) <= 3 for every y in Y. If
    moreover M_n is invertible, then M_m is singular for every m in N with sigma(m) in beta(n, W).

(d) In every case the M_n (n in N) have a common invariant plane. So no orbit of commuting pairs
    (M_(v_1), M_(v_2)) whose matrices generate a field F_8 contains a model; there are 5 such orbits.

*Proof.* (a) By Proposition 27(c4), d is 2 or 3. If d = 3, then R = X_1 and A_u^2 = 0, so
Im A_u^2 = 0. If d = 2, A_u maps R onto Im A_u^2 with kernel R n X_1 of dimension 2, so Im A_u^2 is
a line; it meets ker A_u only if it lies in ker A_u, that is, if A_u^3 = 0. A nilpotent map of rank 3
on F_2^6 with rank A_u^2 = 1 and A_u^3 = 0 has Jordan blocks 3, 2, 1. Outside that case
Im A_u^2 n ker A_u = 0, and Lemma 46(c) gives G_y T q(y) = 0 and, as T is one-to-one on L n D,
M_(n_y) q(y) = 0. q(y) != 0 (Lemma 38(e)) and T q(y) != 0, so M_(n_y) and G_y are singular.

(b) G_y T q(y) = 0 with T q(y) = y + z reads G_y y = G_y^2 y, that is, G_y z = z. If z != 0, then
z != y (T q(y) != 0), z != x0 (else G_y x0 = x0, but G_y x0 = y != x0, as x0 is not in Y), and
z != x0 + y (else G_y z = y + z = x0 != z). So x0, y, z is a basis of X_1. Then G_y + G_y^2 sends x0 to
y + z and kills y and z, so by (5) T M_n q(y) = (G_y + G_y^2) sigma(n) lies in span(y + z) =
span(T q(y)) for every n in N.

(c) If A_u^2 = 0, then R = X_1 and L = 0, so Abar_y = M_(n_y) by Lemma 46(a). A_(h_y) keeps X_1, so its
rank is at least rank G_y + rank Abar_y. Every A_h has rank at most 3: an element of rank 4 would give
dim V <= t + A(1) = 7 by Lemma 30. For the last claim, n is a Case B element with the same X_1, R, N
and W (Lemma 38(c)); in the setting of n, the matrix of m is M_n^(-1) M_m (A_m = T M_m [.] =
(T M_n) M_n^(-1) M_m [.], and T M_n is the map that A_n induces), its Y is beta(n, W), and A_n^2 = 0
as R = X_1 = ker A_n. Part (a) for n says that M_n^(-1) M_m is singular.

(d) If the M_n had no common invariant plane, then A_u^2 = 0 by Corollary 21, and by (a) every M_n
with n in N_Y is singular. If one of them were non-zero, its kernel (if it has rank 1) or its image
(if it has rank 2) would be a plane, invariant under every M_m because the M_m commute with it. So
M_n = 0 for n in N_Y, and as N = span(u) + N_Y and M_u = I, every M_n is 0 or I, and every plane is
invariant. Either way there is a contradiction. If the M_n generate a field K = F_8, then F_2^3 is a
1-dimensional K-space and has no invariant plane, so these orbits are empty. To count them: all
subfields F_8 of M_3(F_2) are conjugate, and the stabiliser of one of them acts on it through its
whole Galois group (of order 3). So the orbits correspond to the Galois orbits of the subspaces
S = span(M_(v_1), M_(v_2)) of K not inside F_2 (GL_2(F_2) is transitive on the pairs that span a given
S): lines span(a) with a outside F_2 (6 of them, 2 orbits) and planes (7 of them, the kernels of
x -> Tr(b x), 3 orbits, from the classes {1}, {a, a^2, a^4}, {a^3, a^6, a^5} of b under squaring).
That gives 5 orbits; the two line orbits are those of the two irreducible cubics. QED

What Corollary 23 does for the search at (6, 3). Part (d) removes 5 orbits outright. Part (a) says
more: an orbit in which span(M_(v_1), M_(v_2)) contains an invertible matrix can hold a model only if
A_u has Jordan blocks 3, 2, 1. These are new constraints for a later search; job m13 did not use
them, so its answers do not depend on Lemma 46 or Corollary 23. Neither result is a contradiction in
the remaining cases, and A(6) <= 7 is still open.

## The split search (job m13, ran on 2026-10-17 and 2026-10-18)

`cube_groups/shape_c.py` takes the CNF of case_b_shapes.py for shape (c) and adds the parity equations
(S) for one representative (M_1, ..., M_(k-1)) of each orbit (the least pair of the orbit). For
t - k <= 3 each equation has at most four variables, so no variables are added. Shape (c) at (t, k)
exists if and only if one of these CNFs is satisfiable (Lemmas 37, 38(b), 39).

The job (m13-shapec-v1, one CPU, 1 GB) was queued on 2026-10-17 and ran from 23:39 UTC on 2026-10-17
to 01:55 UTC on 2026-10-18. Its predictions were written down before it was queued: UNSAT for every
orbit at (3, 2) (2 orbits) and (4, 2) (6 orbits), since A(3) = 3 and A(4) = 4, with (6, 3) and (5, 2)
exploratory. Results:

    (t, k)   instances   budget per instance / group   UNSAT   UNKNOWN   SKIPPED   SAT
    (3, 2)        2           2 / 5 min                   2        -         -       -
    (4, 2)        6           4 / 15 min                  6        -         -       -
    (6, 3)       38           4 / 120 min                 -       30         8       -
    (5, 2)       14           3 / 42 min                 12        2         -       -

Every graded prediction held (the unit tests, the selfcheck and the 8 control instances). At (5, 2)
the two undecided instances were M = 0 and M = I; Lemma 47 of [case-a.md](case-a.md) rules them out
by hand, which gives Corollary 24 there: **no anisotropic system with t = 5 and dim V = 6 has an
element of rank 3 in Case B.** At (6, 3) nothing was decided: 30 orbits reached the 4-minute limit
and the last 8 (in the order of the orbit list) were not reached. A(6) <= 7 is still open. A later
search at (6, 3) can drop the 5 field orbits of Corollary 23(d) and add the conditions of Corollary
23(a). [case-a.md](case-a.md) gives the times of the (5, 2) instances.

## The finer search at k = 2 (shape_c2.py, prepared)

`cube_groups/shape_c2.py` adds to the CNF of shape_c.py (for k = 2 and the chosen M) the values of
Lemma 41(b): unit clauses for sigma(w), beta(v, w), A_w e_0 and A_w e_1, and parity equations for T q
(and T M q in case (iii)) on the columns of A_u. It adds no variables. By Lemma 41, Case B at (t, 2)
exists if and only if one of its 3, 13 or 47 instances (t = 3, 4, 5) is satisfiable. It was meant for
whatever m13 left undecided at t = 5; since Corollary 24 of case-a.md settles Case B at t = 5, it has
not been run and is no longer needed there.

## Computation

The unit tests of `cube_groups/shape_c.py` (which gated its commit) check:

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

The unit tests of `cube_groups/shape_c2.py` check:

- the counts of Lemma 41 against the hand counts above: 2, 10 and 38 pairs (M, q), 3, 13 and 47
  instances, 9, 9 and 20 pairs in cases (i), (ii) and (iii) at t = 5, the centraliser orders for
  t = 3, 4 and 5, and that the orbit sizes add up and divide the centraliser orders;
- that the case of Lemma 41(a) is constant on every C(M)-orbit and that each representative is the
  least vector of its orbit;
- that the added clauses are exactly the predicted number with no new variables, and that coordinates
  built with the fixed values are accepted while every one-bit change of sigma(w), beta(v, w), A_w e_0,
  A_w e_1 or of a column of A_u that T q depends on is rejected.

Lemma 46 and Corollary 23 have no computer check yet. The count of 5 field orbits in Corollary 23(d)
is by hand; shape_c.py lists the orbits and can confirm it in a later test.

## Prior work

Commuting pairs of matrices over finite fields are classical (Feit and Fine, 1960, count them). As for
the earlier notes, searches on 2026-10-15 to 2026-10-18 found nothing on the identity (*), on A(t) or
on Question R other than MV2's own posts, so the use of the commuting matrices M_n here appears to be
new; the tools are elementary, so a specialist may know them. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
