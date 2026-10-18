# Case A in coordinates: a symmetric form and its radical

MV2 of Munim, Inc., 2026-10-18. Added to kakeya-small-fields after version 1.7.12, next to
[case-a.md](case-a.md) and [question-r.md](question-r.md). Numbering continues from case-a.md
(Lemma 50, Lemma 51, Corollary 25). It was researched and written with AI agents working in MV2's
name. Everything here is a proof by hand. When it was written it settled no new case; later the same
day, Lemma 52 of [a5.md](a5.md) grew out of Lemma 51(c) and proved A(5) = 5, and the search designed
below (job m16) ran and agreed (Results of job m16, below). No human mathematician has checked the
proofs. Text CC BY 4.0.

## What changes

- **Lemma 50** writes a system with dim V = t + 1 and an element u for which phi = beta(u, .) maps V
  onto X as data on X alone: a matrix A = A_u, a linear map L : X -> End(X) and a quadratic map
  S : X -> X, tied by four identities. Case A of question-r.md is exactly this situation with
  rank A = t - 2.
- **Lemma 51.** Modulo R = Im A, the map (p, q) -> L(p) q is a **symmetric bilinear form C with values
  in X/R** whose diagonal is the projection p -> [p] and for which x0 = sigma(u) is a unit. Its radical
  Rad lies in R, and R is invariant under every A_h exactly when Rad = R. Rad contains z = sigma(v),
  and S maps the coset x0 + Rad into Rad. In an anisotropic system these facts force
  **dim Rad >= 2**.
- **Corollary 25.** This gives a second proof that Case A needs t >= 5. At t = 5, Case A needs C to
  have rank exactly 3, with Rad = span(sigma(v), S(x0 + z)) a plane in R, and every one of these
  conditions is linear in L once Rad is fixed. That adds new constraints and a split by Rad, for use
  if job m15 leaves some of its 9 instances undecided.

## Setting

As in [case-a.md](case-a.md): X = F_2^t, sigma : V -> X quadratic with polar form beta, h -> A_h
linear, and

    A_(h') sigma(h) = (I + A_h) beta(h, h')                                    (*)

for all h, h' in V. Let dim V = t + 1 and let u in V be such that phi = beta(u, .) maps V onto X; its
kernel is then span(u), since phi(u) = beta(u, u) = 0. Put x0 = sigma(u) and A = A_u. Choose a linear
section s : X -> V with phi(s(p)) = p, so that V = s(X) + span(u), and put

    S(p) = sigma(s(p)),   B(p, q) = beta(s(p), s(q)),   L(p) = A_(s(p)),

so S is a quadratic map X -> X with polar form B, and L : X -> End(X) is linear.

## Lemma 50 (the system in coordinates on X)

**Lemma 50.** For p, q in X and lambda, mu in F_2,

    sigma(s(p) + lambda u) = S(p) + lambda (x0 + p),
    beta(s(p) + lambda u, s(q) + mu u) = B(p, q) + lambda q + mu p,
    A_(s(p) + lambda u) = L(p) + lambda A,

and (*) holds for all h, h' in V if and only if, for all p, q in X,

    (a)  A x0 = 0,
    (b)  L(q) x0 = (I + A) q,
    (c)  L(p) p = p + A S(p),
    (d)  L(q) S(p) = (I + L(p)) B(p, q).

They imply

    (e)  L(p) q + L(q) p = A B(p, q),
    (f)  L(x0) = I + A (I + psi),  where psi(q) = B(x0, q),

and the system is anisotropic if and only if x0 != 0 and, for every p != 0, S(p) is neither 0 nor
x0 + p.

*Proof.* The three formulas follow from beta(s(p), u) = phi(s(p)) = p and beta(u, u) = 0. Put
h = s(p) + lambda u and h' = s(q) + mu u in (*). Using lambda^2 = lambda, the left side is

    L(q) S(p) + lambda L(q)(x0 + p) + mu A S(p) + lambda mu A (x0 + p)

and the right side is

    (I + L(p)) B(p, q) + lambda ((I + L(p)) q + A B(p, q) + A q) + mu (I + L(p)) p + lambda mu A p.

An expression c_0 + lambda c_1 + mu c_2 + lambda mu c_3 vanishes for all lambda, mu in F_2 if and only
if c_0 = c_1 = c_2 = c_3 = 0. The constant terms give (d), the mu terms give (c) and the lambda mu terms
give (a). The lambda terms give

    L(q)(x0 + p) = (I + L(p)) q + A B(p, q) + A q.                              (l)

At p = 0 this is (b). Given (b), (l) is equivalent to (e), and (e) follows from (c): apply (c) at
p + q, p and q and add. So (*) is equivalent to (a) to (d). For (f), put p = x0 in (e) and use (b):
L(x0) q = (I + A) q + A psi(q). Anisotropy is the first formula. QED

Conversely, every A, L and S satisfying (a) to (d) define a system on V = X + F_2 through these
formulas, and phi = beta(u, .) maps it onto X. So **A(t) >= t + 1 by a system that has an element
whose phi is onto** is the same as the existence of such data with S(p) not in {0, x0 + p} for every
p != 0 and x0 != 0. Changing the section s to s + m(.) u, for a linear form m on X, replaces L(p) by
L(p) + m(p) A and S(p) by S(p) + m(p)(x0 + p).

In Case A (rank A = t - 2), take v = s(x0). Then phi(v) = x0, and z = S(x0) = sigma(v) is the vector
of Proposition 25, with ker A = span(x0, z). (The choice of v does not matter: sigma(v + u) = z.)
(f) is Lemma 31 of question-r.md at the pair (u, v), and A_v = L(x0).

## Lemma 51 (the form C and its radical)

Let R = Im A, let [.] : X -> X/R be the projection, and put

    C(p, q) = [L(p) q]    in X/R.

By the last remark of Lemma 50, C does not depend on the section s.

**Lemma 51.** In the setting of Lemma 50:

(a) C is bilinear and symmetric, C(p, p) = [p], and C(x0, q) = C(q, x0) = [q] for all p, q.

(b) Let Rad = {p in X : C(p, q) = 0 for all q}. Then Rad lies in R, and Rad = R if and only if R is
    invariant (A_h R lies in R for every h in V).

(c) z = S(x0) lies in Rad.

(d) If p lies in x0 + Rad, then (I + L(p)) maps X into R, and S(p) lies in Rad.

(e) For r, r' in Rad, B(r, r') lies in Rad, and C(S(r), q) = [B(r, q)] for all q.

(f) If the system is anisotropic and R != X, then z and z' = S(x0 + z) are independent vectors of
    Rad, so dim Rad >= 2. More precisely, S(x0 + r) is neither 0 nor r for every r in Rad.

*Proof.* (a) Bilinearity is clear. By (e) of Lemma 50, L(p) q + L(q) p lies in R, so C is symmetric.
By (c), L(p) p = p + A S(p), so C(p, p) = [p]. By (b), L(q) x0 = q + A q, so C(q, x0) = [q].

(b) If p is in Rad, then [p] = C(p, p) = 0, so p is in R. Every A_h is L(p) + lambda A, and A maps R into
R, so R is invariant if and only if [L(p) r] = 0 for all p in X and r in R, that is, C(p, r) = 0, that
is (by symmetry), R lies in Rad.

(c) By (d) of Lemma 50 with p = x0 and by (f), L(q) z = (I + L(x0)) psi(q) = A (psi(q) + psi(psi(q))),
which lies in R. So C(q, z) = 0 for every q.

(d) Write p = x0 + r with r in Rad. Then C(p, q) = C(x0, q) + C(r, q) = [q], so [(I + L(p)) q] = 0 for all
q. By (d) of Lemma 50, L(q) S(p) = (I + L(p)) B(p, q) lies in R for every q, so C(q, S(p)) = 0.

(e) Take r in Rad. By (d) of Lemma 50, C(q, S(r)) = [B(r, q)] + C(r, B(r, q)) = [B(r, q)]. The left side
is quadratic in r and the right side is linear in r. Taking r = r_1 + r_2 with r_1, r_2 in Rad and
subtracting the instances for r_1 and r_2 gives C(q, B(r_1, r_2)) = 0 for all q.

(f) z = sigma(s(x0)) != 0, as s(x0) != 0. As R != X, the form C(x0, .) = [.] is not 0, so x0 is not in
Rad. For r in Rad, p = x0 + r is then not 0, so anisotropy gives S(p) != 0 and S(p) != x0 + p = r, and
S(p) lies in Rad by (d). For r = 0 this is z != 0. For r = z it says z' = S(x0 + z) lies in Rad and is
neither 0 nor z. QED

The proof uses only (*), anisotropy and R != X; the rank of A is not used.

## Corollary 25 (what Case A needs)

**Corollary 25.** Let (sigma, alpha) be an anisotropic system with dim V = t + 1 and an element u in
Case A (rank A_u = t - 2, phi onto X), and let C and Rad be as in Lemma 51.

(a) 2 <= dim Rad <= t - 2, so t >= 4.

(b) If t = 4, Rad = R is invariant, and Lemma 27(c) gives dim V <= M(2) + A(2) = 4, a
    contradiction. So t >= 5.

(c) If t = 5, then Rad = span(z, z') is a plane in R, not all of R, and C has rank exactly 3:
    p -> C(p, .) has kernel Rad. Rad meets ker A = span(x0, z) in span(z) only.

(d) For every t with A(t - 2) <= t - 2 (so for t <= 6, and for every t if A(s) = s for all s), Rad is
    not all of R: some L(p) maps some vector of R outside R.

*Proof.* (a) Lemma 51(b) and (f); R has dimension t - 2 < t. (b) dim Rad >= 2 = dim R, and Rad lies in
R. Lemma 27(c) applies with d = 2 and needs M(2) = A(2) = 2. (c) and (d): if Rad = R, then R is
invariant (Lemma 51(b)), of dimension d = t - 2, and Lemma 27(c) gives
dim V <= M(2) + A(t - 2) <= 2 + (t - 2) = t, a contradiction. At t = 5 this gives
span(z, z') in Rad, Rad != R, with dimensions 2 <= dim Rad < 3, so Rad = span(z, z'). Neither x0 nor x0 + z is in
Rad, because C(x0, .) = C(x0 + z, .) = [.] is not 0. QED

Corollary 25(b) reproves the first part of Proposition 25 (Case A needs t >= 5) without Lemma 32. It
uses Lemma 27(c) instead, and so the values M(2) = A(2) = 2.

## What this adds to the search for Case A at t = 5

In the normal form of Lemma 48 of [case-a.md](case-a.md) (x0 = e_0, z = e_1, A_u = C_i fixed, one
instance per orbit i of Lemma 49), R = Im C_i is known. Lemma 51(c) adds 2 x 5 linear conditions on
the maps A_(v_j): the class of A_(v_j) e_1 in X/R is 0 for every basis vector v_j. Corollary 25(c)
says more. Rad is one of the planes of R through e_1 that miss e_0 and e_0 + e_1: three planes if e_0
is not in R, two if it is. Once Rad is fixed, C(r, .) = 0 for r in Rad is a set of 20 linear
conditions on the A_(v_j) (the 10 above among them), and S(x0 + r) in Rad \ {0, r} for r in Rad
gives four more conditions, which are not linear. A
search split by (orbit of A_u, plane Rad) has at most 9 x 3 = 27 instances, each with these
conditions. These are consequences of (*), so they remove no models; they only give the solver
facts that it would otherwise have to find for itself. Job m15 does not use them, so its answers do
not depend on Lemmas 50 and 51.

`cube_groups/case_a2.py` builds these 23 instances at t = 5 (and 2 control instances at t = 4, where
Corollary 25(b) predicts UNSAT). It went into the repository through a commit gated by its unit
tests, which compare each added constraint with a direct check on random coordinates. It was queued as
job m16 on 2026-10-18, with its predictions written down first. Its UNSAT answers count only together
with the hand proofs of Lemma 51 and Corollary 25, so m15 stays the primary search and m16 is a cross-check.
A verified SAT answer from either job would be a real anisotropic system with t = 5 and dim V = 6.

## Results of job m16 (added 2026-10-18)

Job m16-caseb-v1 ran on 2026-10-18 from 08:22 to 08:26 UTC on one CPU (cadical195), after job m15
(06:59 to 07:02 UTC, reported in [a5.md](a5.md)) and after Lemma 52 was found. Its predictions were
written at about 04:30 UTC, before either job ran:

    t    instances   prediction            result
    4        2       UNSAT (control)       2 UNSAT
    5       23       exploratory           23 UNSAT, each in under 1 second (0.4 to 0.6 s wall)

The selfcheck (planes: 0, 2 and 23 for t = 3, 4 and 5; 3 planes per orbit of A_u with e_0 outside
R and 2 with e_0 in R at t = 5) and the 7 unit tests passed, and every graded prediction held. No
instance was UNKNOWN or SKIPPED, so the consistency check with m15 is complete: every orbit is UNSAT
in both encodings. The ungraded guess that m16's instances would be faster than m15's cannot be
told apart at this size (all took under a second in both jobs).

So, conditional on Lemma 51 and Corollary 25, the search finds no Case A element at t = 5, which
Lemma 52 of a5.md proves by hand and job m15 finds without these conditions. The three routes agree.
This is a computer check without proof certificates.

## What it does not settle

Lemma 51 does not rule out Case A at t = 5 by itself. With Rad a plane, the form C on X / Rad
(dimension 3, values in F_2^2) is non-degenerate, has diagonal [.] and unit [x0], and kills R / Rad
against R + span(x0). Such forms exist, so a contradiction needs more of (d) of Lemma 50 than its
reduction modulo R. Lemma 52 of a5.md supplies it: the coset maps of Lemma 51(d) at p = x0 and
p = x0 + z, restricted to R, have rank at most 1, and that is already a contradiction. Whether Rad is
invariant under every A_h is still not known; it is no longer needed at t = 5.

## Prior work

As for the earlier notes, searches on 2026-10-15 to 2026-10-18 found nothing on the identity (*), on
A(t) or on Question R other than MV2's own posts. Writing a structure on V = X + F_2 as a product on
X is a standard device, and a specialist may know these tools. Please open an issue at
https://github.com/munimtechnologies/kakeya-small-fields if this is known, or if you find an error.
