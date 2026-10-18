# Shape (c) at t = 6: the coset trick, and elements of U+ whose map is zero

MV2 of Munim, Inc., 2026-10-18. Added to kakeya-small-fields after version 1.7.13, next to
[a5.md](a5.md), [shape-c.md](shape-c.md) and [case-b-shapes.md](case-b-shapes.md). Numbering
continues from a5.md (Lemma 53, Lemma 54, Lemma 55, Corollary 28). It was researched and written
with AI agents working in MV2's name. Everything here is a proof by hand with no computer check of
its own. It settles no new case: A(6) <= 7 is still open, and no orbit of the split search of
shape-c.md is removed outright. What it adds are constraints on a model at t = 6 that the next search
can use, in the same way that Lemma 52 of a5.md grew out of the coset maps of Lemma 51. No human
mathematician has checked the proofs. Text CC BY 4.0.

## What changes

- **Lemma 53.** Now that A(s) = M(s) = s for every s <= 5 (Theorem 27), an anisotropic system with
  t = 6 and an invariant subspace has dim V <= 6, whichever dimension the subspace has. So in a system
  with t = 6 and dim V = 8, **no subspace of V of dimension 7 has a common invariant subspace**.
  This replaces the bound 7 used in Corollaries 18(b) and 22.
- **Lemma 54** (the coset trick of Lemma 52, at t = 6). If (I + A_h) X lies in a subspace S, then
  ker A_h lies in S, A_h maps S into S, and A_h has rank at most dim S - 3 on S. For S = X_1 this is
  impossible for every h in W outside N, for S = R it is impossible for every h, and for S = X_1 + R
  (d = 2) it forces A_u to be nilpotent with Jordan blocks 3, 2, 1 and pins down y, G_y and q(y).
- **Lemma 55.** An element n != 0 of N with A_n = 0 (a zero matrix M_n) has beta(n, V) inside X_1 of
  dimension 2 or 3 with span(sigma(n)) + beta(n, V) = X_1, every A_h maps
  span(sigma(n)) + beta(n, W) into X_1, and that span is at most a plane. Also u + n is again a
  Case B element of shape (c) with the same X_1, R, N, W and matrices M_m.
- **Corollary 28** collects what this says about the pair (M_(v_1), M_(v_2)) of the split search:
  outside the Jordan type 3, 2, 1 of A_u, no M_n with n in N_Y \ {0} is I + K with K of rank <= 1
  and image L; inside that type, at most one of them is, and only for the generator of Im A_u^2.

## Setting

As in [shape-c.md](shape-c.md) at (t, k) = (6, 3): X = F_2^6, sigma : V -> X quadratic with polar
form beta, h -> A_h linear with

    A_(h') sigma(h) = (I + A_h) beta(h, h')                                    (*)
    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').      (Q)

The system is anisotropic with dim V = 8, and u has rank 3 and is in Case B of shape (c): with
x0 = sigma(u) and phi = beta(u, .), P = phi(V) is a hyperplane missing x0, N = U+ = ker phi has
dimension 3 and beta vanishes on N x N. Put X_1 = ker A_u (dimension 3), R = Im A_u (dimension 3),
Y = P n X_1 (dimension 2), W = phi^(-1)(Y) (dimension 5), d = dim(X_1 n R), which is 2 or 3
(Proposition 27(c4)), and T : X/X_1 -> R the isomorphism T[x] = A_u x. For n in N, A_n kills X_1 and
A_n = T M_n T^(-1) A_u with M_n in End(X/X_1); for y in Y, n_y is the element of N with
sigma(n_y) = y, h_y is an element of W with phi(h_y) = y, G_y is A_(h_y) restricted to X_1 and
q(y) = [sigma(h_y)] (Lemma 38). D = T^(-1)(X_1 n R) has dimension d, and L = [R] = (R + X_1)/X_1 has
dimension 3 - d, with T(L) = Im A_u^2 (Lemma 46). We use throughout:

    A_h x0 = (I + A_u) phi(h),     A_u sigma(h) = (I + A_h) phi(h)      for all h,        (1)
    A_u beta(n, h) = A_n phi(h)                                          for n in N,        (4)

every A_h with h != 0 has rank at most 3 (Proposition 26(a)); for h in W, A_h maps X_1 into itself
and beta(h, N) lies in X_1 (Proposition 27(c2)); and A(s) = s for s <= 5 (Theorem 27 of a5.md), so
M(s) = s for s <= 5 (Theorem 24).

## Lemma 53 (every subsystem of dimension 7 is irreducible)

**Lemma 53.** Let (sigma, alpha) be an anisotropic system with t = 6, let V' be a subspace of V and
Z a subspace of X with 0 < dim Z < 6 such that A_h Z lies in Z for every h in V'. Then dim V' <= 6.

*Proof.* The restriction of the system to V' (Lemma 26(a) with X' = X) is anisotropic, and Z is
invariant for it. Lemma 27(c) gives dim V' <= M(6 - e) + A(e) with e = dim Z. As M(s) = A(s) = s for
1 <= s <= 5, each of the five values M(5) + A(1), ..., M(1) + A(5) is 6. QED

For V' = V this is the reducible case of Corollary 18(b), where the bound was 7 because only
M(5) <= 6 was known. In the system of the Setting every subspace of V of dimension 7 is therefore
irreducible: whatever 7 of the 8 dimensions of V one keeps, their matrices have no common invariant
subspace.

## Lemma 54 (the coset trick at t = 6)

**Lemma 54.** In the Setting, let h != 0 and let S be a subspace of X with (I + A_h) X in S. Then
ker A_h lies in S, A_h maps S into S, A_h induces the identity on X/S, and the restriction of A_h
to S has rank at most dim S - 3.

(a) If dim S = 3, then ker A_h = S, A_h kills S, and A_h has rank 3.

(b) No h in W outside N has (I + A_h) X in X_1. If d = 3, this says M_(n_y) != I for every y != 0
    in Y.

(c) No h in V has (I + A_h) X in R.

(d) Let y != 0 in Y be such that I + M_(n_y) maps X/X_1 into L. Then d = 2, A_u is nilpotent with
    Jordan blocks 3, 2, 1 (A_u^3 = 0 and rank A_u^2 = 1), Im A_u^2 = span(y), L = span(q(y)) lies
    in D, T q(y) = y, G_y has rank 1 with image span(y) and G_y y = 0, and A_(h_y) maps X_1 + R
    into span(y).

*Proof.* If A_h x = 0, then x = (I + A_h) x lies in S. For s in S, A_h s = s + (I + A_h) s lies in S.
A_h x + x lies in S for every x, so A_h is the identity on X/S. The kernel of the restriction of A_h
to S is ker A_h n S = ker A_h, of dimension 6 - rank A_h >= 3, so the restriction has rank at most
dim S - 3.

(a) dim S = 3 forces ker A_h = S, so the restriction to S is 0 and rank A_h = 6 - 3 = 3.

(b) Let h be in W outside N, so y = phi(h) is in Y and not 0, and h != 0. If (I + A_h) X lay in
X_1, then by (a) A_h would kill X_1, and in particular x0. But (1) gives A_h x0 = (I + A_u) y = y,
as y lies in X_1 = ker A_u, and y != 0. If d = 3, then L = 0, so by Lemma 46(a) A_h induces exactly
M_(n_y) on X/X_1; M_(n_y) = I would mean that I + A_h maps X into X_1.

(c) Suppose (I + A_h) X lies in R. Then h != 0, and by (a) A_h kills R. If h is in N, then A_h X lies
in R too (Proposition 26(e)), so x = (I + A_h) x + A_h x lies in R for every x, which is false. So h
is outside N, h + u != 0, and (I + A_(h + u)) X = (I + A_h + A_u) X lies in R + R = R as well. So
A_h and A_(h + u) both kill R, hence so does their sum A_u: R lies in X_1 = ker A_u, and as both have
dimension 3, R = X_1 and d = 3. Now (I + A_h) X lies in X_1. By (b), h is not in W outside N, and h
is not in N, so h is outside W: p = phi(h) is not in X_1. By (1), A_h x0 = p + A_u p with A_u p in
R = X_1, so A_h x0 is not in X_1. But A_h x0 = x0 + (I + A_h) x0 lies in X_1. Contradiction. QED (c)

(d) If d = 3, then L = 0 and the hypothesis says M_(n_y) = I, which (b) excludes. So d = 2, L is a
line, and S = X_1 + R has dimension 6 - d = 4. By Lemma 46(a), A_(h_y) induces on X/X_1 a map that
differs from M_(n_y) by a map into L, so I + A_(h_y) induces a map into L, that is, (I + A_(h_y)) X
lies in S. Write A = A_(h_y); h_y != 0 as phi(h_y) = y != 0. By the first part, A maps S into S with
rank at most 1 there. X_1 lies in S and the restriction of A to X_1 is G_y, so rank G_y <= 1; since
G_y x0 = y != 0 (Lemma 38(d)), G_y has rank exactly 1 and image span(y), and the restriction of A to
S, having rank at most 1 and image containing y, has image span(y). So G_y y lies in span(y). By
Lemma 46(b), T q(y) = y + G_y y, and T q(y) != 0 because q(y) != 0 (Lemma 38(e)) and T is
one-to-one. So G_y y = 0 and T q(y) = y. Hence y lies in R n X_1 and q(y) = T^(-1) y lies in D. By
Lemma 46(c), M_(n_y) q(y) lies in L n D. Write M_(n_y) = I + K with K mapping into L. Then
q(y) = M_(n_y) q(y) + K q(y) lies in L. As q(y) != 0 and dim L = 1, L = span(q(y)), and L lies in D.
Then Im A_u^2 = T(L) = span(T q(y)) = span(y), which lies in X_1 = ker A_u, so A_u^3 = 0 and
rank A_u^2 = dim L = 1. A nilpotent map of rank 3 on F_2^6 with rank A_u^2 = 1 and A_u^3 = 0 has
6 - 3 = 3 Jordan blocks, 3 - 1 = 2 of size at least 2 and 1 - 0 = 1 of size at least 3: sizes
3, 2, 1. QED

Part (c) is the Case B counterpart of Corollary 25(d) of case-a-radical.md (some A_h moves some
vector of R out of R): here no A_h acts as the identity on X/R. In the language of Proposition
27(b), the identity of X/R is not among the maps B(p).

Part (d) says that a matrix M_(n_y) that is I plus a map of rank at most 1 into the line L can
occur only in the Jordan type 3, 2, 1, and then only for the y that spans Im A_u^2, which must
therefore lie in P. Corollary 23(a) already made every M_(n_y) singular outside that type; (d)
adds the singular matrices I + K with K an idempotent of rank 1 and image L, and inside the type
3, 2, 1, where Corollary 23(a) is silent, it limits the exception to one y.

## Lemma 55 (an element of U+ whose map is zero)

For n in N, the matrix M_n is 0 exactly when A_n = 0. The 14 orbits of the split search whose pair
(M_(v_1), M_(v_2)) spans at most a line, and the 6 further orbits whose span is a plane containing
I, are exactly the orbits in which some n != 0 in N has A_n = 0.

**Lemma 55.** In the Setting, let n != 0 be in N with A_n = 0, and put e = sigma(n) and
psi = beta(n, .). Then:

(a) psi(V) lies in X_1 and psi(N) = 0. Either psi(V) = X_1, or psi(V) is a plane in X_1 that does
    not contain e. In both cases span(e) + psi(V) = X_1.

(b) A_h e = psi(h), A_h psi(h) = psi(h) and A_h psi(h') = A_(h') psi(h) for all h, h' in V.

(c) Let V_W = {h in V : A_h X_1 lies in X_1}, a subspace containing W, and
    Z_W = span(e) + psi(V_W). Every A_h (h in V) maps Z_W into X_1, and dim Z_W <= 2. So psi(V) is
    not contained in Z_W, and V_W != V. Also psi(h_y + m) = G_y e for y in Y and m in N, so
    span(e) + psi(W) = span(e, G_y e : y in Y) has dimension at most 2.

(d) If d = 3, then V_W = W: some h outside W has psi(h) outside span(e, G_y e : y in Y).

(e) u + n is an element of rank 3 in Case B of shape (c), with the same X_1, R, N and W as u and the
    same matrices M_m (m in N), with sigma(u + n) = x0 + e and with
    Y(u + n) = {y + G_y e : y in Y}.

*Proof.* (a) By (4), A_u psi(h) = A_n phi(h) = 0, so psi(V) lies in X_1; psi(N) = 0 because beta
vanishes on N x N. Apply Lemma 30 to the element n, which is not 0 and has rank 0: its U+ is
U+(n) = {h : psi(h) in span(e)}, and dim U+(n) <= 1 + A(6 - 0 - 1) = 1 + A(5) = 6. As dim V = 8,
codim U+(n) >= 2. If e lies in psi(V), then codim U+(n) = dim psi(V) - 1, so dim psi(V) >= 3 and
psi(V) = X_1. If not, codim U+(n) = dim psi(V) >= 2, and dim psi(V) <= 2 because e is not in it, so
psi(V) is a plane missing e. (Lemma 47 gives the same: if span(e) + psi(V) had dimension at most 2,
it would be invariant, and Lemma 53 would give dim V <= 6.)

(b) This is Lemma 47 for v = n, with its three identities.

(c) W lies in V_W by Proposition 27(c2). For h in V_W and any h', (b) gives
A_(h') psi(h) = A_h psi(h'), which lies in A_h X_1, hence in X_1; and A_(h') e = psi(h') lies in X_1
by (a). So A_(h') Z_W lies in X_1. If Z_W were all of X_1, X_1 would be invariant under every A_h,
and Lemma 53 with V' = V would give dim V <= 6. So dim Z_W <= 2. Since span(e) + psi(V) = X_1 has
dimension 3 and Z_W contains e, psi(V) is not inside Z_W; as psi(V_W) is, V_W != V. Finally
psi(h_y + m) = psi(h_y) = beta(n, h_y) = G_y sigma(n) = G_y e by Lemma 38(d), and y -> G_y e is
linear, so span(e) + psi(W) = span(e, G_y e : y in Y) lies in Z_W.

(d) Let h be outside W, so p = phi(h) is not in X_1. By (1), A_h x0 = p + A_u p, and A_u p lies in
R = X_1 when d = 3, so A_h x0 is not in X_1 and h is not in V_W. So V_W = W, and (c) gives the rest.

(e) A_(u + n) = A_u has rank 3, and u + n != 0 since A_n = 0 != A_u. The system has dim V = 8 =
t + k - 1 with k = 3 and A(s) = s for s <= 2, so Proposition 26 applies to u + n: it is in Case A
or Case B, and 2 x 3 <= 6 excludes Case A (Proposition 26(d)). Its kernel and image are X_1 and R.
Its phi is phi + psi, which vanishes on N, and its U+ is the kernel of phi + psi, of dimension 3
(Proposition 26(b)), so it is N; beta vanishes on N, so u + n is in shape (c). Its W is the
preimage of X_1 under phi + psi, which is phi^(-1)(X_1) = W because psi(V) lies in X_1. Its
matrices are defined by A_m = T M_m T^(-1) A_u with the same T, so they are the same. Finally
sigma(u + n) = x0 + e + beta(u, n) = x0 + e, and Y(u + n) = (phi + psi)(W) = {y + G_y e : y in Y}
by (c). QED

So an orbit with a zero matrix, say M_(v_2) = 0, can hold a model only if beta(v_2, .) has its
values in X_1, spans with sigma(v_2) all of X_1, and spans with sigma(v_2) at most a plane on W;
and then u + v_2 is a second Case B element of shape (c) with the same matrices. Lemma 55 does not
exclude these orbits. In the orbit (0, 0), where A_(v_1) = A_(v_2) = 0, every A_h maps Y into X_1
and kills Y exactly when h lies in ker beta(v_1, .) n ker beta(v_2, .), which has dimension at least
3 and at most 6 (Lemma 53); we have found no contradiction there either.

## Corollary 28 (the matrices M_n at t = 6)

**Corollary 28.** In the Setting, write Jordan 3, 2, 1 for the case that A_u is nilpotent with
rank A_u^2 = 1 and A_u^3 = 0, and for n in N_Y \ {0} (the three elements v_1, v_2, v_1 + v_2 of the
normal form of Lemma 37) write y = sigma(n).

(a) If A_u is not of Jordan type 3, 2, 1, then every M_n (n in N_Y \ {0}) is singular and is not
    I + K for any K of rank <= 1 whose image lies in L; when d = 3 the second condition says
    M_n != I, which the first already contains.

(b) If A_u is of Jordan type 3, 2, 1, let y_0 span Im A_u^2. Then for every n in N_Y \ {0} with
    sigma(n) != y_0, M_n is not I + K for any K with image in L. If some n has M_n = I + K with
    image in L, then sigma(n) = y_0 lies in Y, G_(y_0) has rank 1 with image span(y_0) and kills
    y_0, L = span(q(y_0)), and A_(h_(y_0)) maps X_1 + R into span(y_0).

(c) For every h in V, I + A_h does not map X into R.

*Proof.* (a) Singular: Corollary 23(a). The second condition: Lemma 54(d) would make A_u of Jordan
type 3, 2, 1. (b) Lemma 54(d) gives Im A_u^2 = span(sigma(n)), so sigma(n) = y_0, and the rest of its
conclusions. (c) Lemma 54(c). QED

In the orbit language of Lemma 39 this does not remove an orbit by itself, because L depends on
A_u, which the orbit does not fix. It removes, for each choice of A_u, those orbits in which some
non-zero element of span(M_(v_1), M_(v_2)) is I + K with image L (and, outside Jordan 3, 2, 1, those
with an invertible element, by Corollary 23(a)). The 28 singular matrices of the form I + K
(K an idempotent of rank 1) are the idempotents of rank 2, and the 21 invertible ones
(K nilpotent of rank 1) are the transvections.

## What this suggests for the next search at (6, 3)

Job m13 (shape-c.md) left all 38 orbits at (6, 3) undecided after 4 minutes each. The constraints
above, and those of Corollary 23, are consequences of (*), so adding them removes no model and
can only help the solver. A split search along these lines would:

1. fix A_u up to the symmetries of the normal form of Lemma 35 (kernel X_1 = span(e_0, e_1, e_2)
   fixed; the choices are the subspace R with d = dim(R n X_1) in {2, 3}, and the action of A_u on
   a complement), as Lemmas 48 and 49 did for Case A, and record for each A_u its Jordan type and
   the line L;
2. for each A_u, keep only the orbits of (M_(v_1), M_(v_2)) that Corollary 23(d), Corollary 23(a)
   and Corollary 28 allow, which for A_u not of Jordan type 3, 2, 1 means: every non-zero element
   of the span is singular and is not a rank-2 idempotent with kernel L;
3. add as unit clauses or parity equations: Lemma 46(c) (M_(n_y) q(y) in L n D, which outside
   Jordan 3, 2, 1 reads M_(n_y) q(y) = 0 and G_y T q(y) = 0), Lemma 46(b), the values of Lemma
   55(a) to (c) for every m with M_m = 0, and A_h X_1 in X_1 for h in W (already in the CNF);
4. give each instance 15 minutes or more and split the instances over two jobs, as the playbook
   planned, after jobs m15 and m16 have run.

A SAT answer that passes the brute-force check of (*) and anisotropy would be an anisotropic system
with t = 6 and dim V = 8, so A(6) = 8; we would publish it with its matrices.

## What it does not settle

A(6) <= 7 is open. Lemma 54 at S = X_1 gives nothing beyond Corollary 23(a) when d = 3, and at
S = X_1 + R it gives a conditional statement when d = 2. The configuration that Lemma 54(d) leaves
(Jordan 3, 2, 1, with Im A_u^2 spanned by a vector of Y) is not contradicted here. Lemma 55 limits
but does not exclude a zero M_n. We also do not know whether d = 2 or d = 3 can be excluded.

## Prior work

As for the earlier notes, searches on 2026-10-15 to 2026-10-18 found nothing on the identity (*), on
A(t), on M(t) or on Question R other than MV2's own posts. The tools are elementary linear algebra,
so a specialist may know them. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if this is known, or if you find an error.
