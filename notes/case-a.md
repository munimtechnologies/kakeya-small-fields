# t = 5: Case B is impossible at rank 3, and A(5) = 5 now rests on Case A alone

MV2 of Munim, Inc., 2026-10-18. Added to kakeya-small-fields after version 1.7.11, next to
[shape-c.md](shape-c.md), [case-b.md](case-b.md) and [question-r.md](question-r.md). Numbering
continues from shape-c.md (Lemma 47, Corollary 24, Lemma 48, Lemma 49). It was researched and
written with AI agents working in MV2's name. Lemma 47 and the deduction of Corollary 24 are proofs
by hand; Corollary 24 also rests on 12 UNSAT answers of a SAT solver (job m13, no proof certificates
saved). `case_a.py` builds the next search and checks the hand counts of Lemma 49; it runs in job
m15, and it goes into `cube_groups/` only through a commit that its unit tests gate. No human
mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

## What changes

- **The split search of shape-c.md ran** (job m13-shapec-v1, 2026-10-17 23:39 to 2026-10-18 01:55 UTC,
  one CPU). Every graded prediction held (9 of 9). At (t, k) = (5, 2) it refuted 12 of the 14
  instances, one per similarity class of the matrix M of Lemma 39, in 8 to 128 seconds each. The two
  left undecided after 3 minutes were M = 0 and M = I. At (6, 3), 30 of the 38 orbits reached the
  4-minute limit and 8 were not reached, so A(6) <= 7 is still open.
- **Lemma 47** (by hand). If some A_v is 0, then sigma(v) and the values beta(v, .) span a subspace that
  is invariant under every A_h, as long as that span has dimension at most 2.
- **Corollary 24.** This disposes of M = 0 and M = I, so **no anisotropic system with t = 5 and
  dim V = 6 has an element of rank 3 in Case B**. Every element of rank 3 of such a system is in
  Case A, and **A(5) = 5 holds if and only if Case A does not occur at t = 5**.
- **Lemmas 48 and 49** put a Case A element at t = 5 into a normal form, with A_u fixed to one of 9
  matrices (counted by hand and by `case_a.py`). The exact search over these 9 instances
  (job m15-casea-v1) was queued on 2026-10-18, with its predictions written down first. If all 9 are
  UNSAT, then A(5) = 5, and so M(5) = 5.

## Setting

As in [shape-c.md](shape-c.md): X = F_2^t, sigma : V -> X quadratic with polar form beta, and
h -> A_h linear with

    A_(h') sigma(h) = (I + A_h) beta(h, h')                                    (*)
    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').      (Q)

A(t) is the largest dim V of an anisotropic system, and M(t) is the number of Theorem 24 of
finite-groups.md. A(s) = s for s <= 4 (Theorem 26), so M(s) = s for s <= 4 (Theorem 24). For u in V
put x0 = sigma(u), phi = beta(u, .), X_1 = ker A_u, R = Im A_u. A subspace Z of X is *invariant* if
A_h Z lies in Z for every h; by Lemma 27(c), an anisotropic system with an invariant subspace of
dimension d, 0 < d < t, has dim V <= M(t - d) + A(d).

## Lemma 47 (a zero map)

**Lemma 47.** Let (sigma, alpha) be a system and v in V with A_v = 0. Put e = sigma(v) and
psi = beta(v, .). Then for all h, h' in V

    A_h e = psi(h),     A_h psi(h) = psi(h),     A_h psi(h') = A_(h') psi(h).

If Z = span(e) + psi(V) has dimension at most 2, then Z is invariant.

*Proof.* (*) with h -> v gives A_(h') e = (I + A_v) psi(h') = psi(h'). (*) with h' -> v gives
0 = A_v sigma(h) = (I + A_h) psi(h). (Q) with h_1 = v, h_2 = h gives A_(h') psi(h) =
A_v beta(h, h') + A_h psi(h') = A_h psi(h'). If psi(V) lies in span(e), then A_h e = psi(h) lies in
span(e) for every h, so Z = span(e) is invariant. Otherwise take h_0 with z_0 = psi(h_0) outside
span(e). Then e != 0 (if e = 0, the first identity gives psi = 0), so Z = span(e, z_0). A_(h_0) maps
e to z_0 and z_0 to z_0, so A_(h_0) Z lies in Z. For any h, A_h e = psi(h) lies in Z, and
A_h z_0 = A_(h_0) psi(h) lies in A_(h_0) Z, which lies in Z. QED

The bound on dim Z is needed: the third identity alone does not keep psi(V) inside Z when psi(V) is
larger.

## Corollary 24 (Case B at t = 5)

**Corollary 24.** Let (sigma, alpha) be an anisotropic system with t = 5 and dim V = 6.

(a) No element of rank 3 is in Case B.

(b) Some element has rank 3, and every element of rank 3 is in Case A. So A(5) = 5 holds if and only
    if no anisotropic system with t = 5 and dim V = 6 has an element of rank 3 in Case A.

*Proof.* (a) Let u have rank 3 and be in Case B, so k = 2, N = U+ = span(u, v) and, by Proposition 27(c)
of case-b.md, u is in shape (c). By Lemmas 35, 37 and 39 we may take the system in the normal form of
shape (c) with M = M_v any chosen matrix of its similarity class in M_3(F_2). For 12 of the 14
classes, job m13 found the CNF of that normal form unsatisfiable (Results below). The other two are
M = 0 and M = I. If M = 0, then A_v = T M T^(-1) A_u = 0; put n = v. If M = I, then A_v = A_u; put
n = u + v, which is not 0, so A_n = 0. In both cases n is a non-zero element of N with A_n = 0. Its
value sigma(n) lies in X_1 (Proposition 26(e)) and is not 0. (Q) with h_1 = u, h_2 = n and h' = h gives
A_h beta(u, n) = A_u beta(n, h) + A_n phi(h); here beta(u, n) = phi(n) = 0 and A_n = 0, so
A_u beta(n, h) = 0 and beta(n, V) lies in X_1. So Z = span(sigma(n)) + beta(n, V) lies in X_1, which has
dimension 2, and Z != 0. By Lemma 47, Z is invariant, with 0 < dim Z <= 2 < 5. Lemma 27(c) gives
dim V <= max(M(4) + A(1), M(3) + A(2)) = 5, a contradiction.

(b) If alpha(V) is reducible, Lemma 27(c) gives dim V <= max over 0 < d < 5 of M(5 - d) + A(d) = 5. If it
is irreducible and every element has rank <= 2, Lemmas 28 and 29 give dim V <= 5. Every A_h with
h != 0 is singular, and an element of rank 4 gives dim V <= 5 + A(0) = 5 (Lemma 30). So some element u
has rank 3, and then k = 2 and dim V = t + k - 1. By Proposition 26 of tight-cases.md (which needs
A(1) = 1), u is in Case A or Case B, and by (a) it is in Case A. Finally, an anisotropic system with
t = 5 and dim V >= 6 restricts (Lemma 26(a)) to one with dim V = 6, and A(5) >= 5. QED (computer-assisted
through job m13; uses Theorem 3.5 of de Seguins Pazzis through Lemma 29, as Proposition 24 does.)

The same argument shows, for every t <= 5, that in Case B with k = 2 neither M nor M + I is 0. For
t = 6 it would need M(5) = 5. Lemma 47 does not settle the orbits of shape (c) at (6, 3) in which
some M_n is 0 or I, because there X_1 has dimension 3.

## Results of job m13-shapec-v1

The job ran `cube_groups/shape_c.py` (shape-c.md) on one CPU with 1 GB, CaDiCaL 1.9.5 through
python-sat. The 8 unit tests passed, and the selfcheck passed: 2, 16, 88, 512 and 7,456 commuting
tuples; 2, 6, 9, 14 and 38 orbits; orbit times stabiliser equal to 1,008 for each of the 38 orbits
of pairs of 3 x 3 matrices; 1 + 13 orbits spanning at most a line.

    (t, k)   instances   budget per instance / group   UNSAT   UNKNOWN   SKIPPED   SAT
    (3, 2)        2           2 / 5 min                   2        -         -       -
    (4, 2)        6           4 / 15 min                  6        -         -       -
    (6, 3)       38           4 / 120 min                 -       30         8       -
    (5, 2)       14           3 / 42 min                 12        2         -       -

The (3, 2) and (4, 2) instances took under half a second each, as predicted (UNSAT, since A(3) = 3
and A(4) = 4). At (5, 2), the 12 decided classes took 8.1 to 127.2 seconds of solver time; the two
undecided ones, after 180 seconds, were the zero
matrix and the identity, which Lemma 47 now handles by hand. Our guess, written before the run, that
the orbits of span dimension at most 1 would be the fastest was wrong: at (5, 2) they were the only
ones left. No instance anywhere came back SAT.

## Lemma 48 (a normal form for Case A)

Recall Case A from question-r.md: dim V = t + 1, u has rank t - 2, and phi maps V onto X with kernel
span(u). Take v with phi(v) = x0 and put z = sigma(v). Proposition 25 shows ker A_u = span(x0, z) with
z outside span(x0). Lemma 31 gives Im(I + A_v) in R, and A_v z = A_v sigma(v) = 0, so
z = (I + A_v) z lies in R.

**Lemma 48.** Let G be the group of g in GL(X) with g e_0 = e_0 and g e_1 = e_1. If some anisotropic
system with dim X = t and dim V = t + 1 has an element u in Case A, then for each matrix C in the
G-conjugacy class of the matrix of A_u it has one with bases e_0, ..., e_(t-1) of X and v_0, ..., v_t of
V such that

    v_0 = u,  sigma(v_0) = e_0,  beta(v_0, v_i) = e_(i-1) (1 <= i <= t),  sigma(v_1) = e_1,  A_(v_0) = C,

where C kills e_0 and e_1, has rank t - 2, and has e_1 in its image.

*Proof.* Put e_0 = x0 and e_1 = z, extend to a basis of X, and take v_0 = u, v_1 = v, and v_i with
phi(v_i) = e_(i-1) for 2 <= i <= t. Since phi maps v_1, ..., v_t onto a basis of X and kills u, these
t + 1 vectors are a basis of V. The facts above give A_u e_0 = A_u e_1 = 0, rank t - 2 and e_1 in R.
For g in G, replace e_j by e'_j = g e_j for j >= 2 and v_i (i >= 2) by elements with phi(v'_i) = e'_(i-1);
e_0, e_1, v_0 and v_1 stay. Every condition still holds, and the matrix of A_u becomes g^(-1) A_u g.
QED

So Case A at t exists if and only if, for one G-orbit of such matrices C, the CNF of sat_aniso.py with
these values fixed by unit clauses is satisfiable. The search fixes sigma(u), sigma(v), all of
beta(u, .) and all of A_u.

## Lemma 49 (the orbits of A_u)

**Lemma 49.** The matrices C of Lemma 48 number 1, 42 and 5,880 for t = 3, 4 and 5, and G has order
4, 96 and 10,752. They fall into 1, 3 and 9 orbits, of sizes [1], [6, 12, 24] and
[168, 168, 168, 448, 672, 672, 896, 1344, 1344].

*Proof.* C induces an injective map X/X_1 -> X with image R, a subspace of dimension t - 2 that
contains e_1; there are 1, 7 and 35 such subspaces and |GL_(t-2)(F_2)| = 1, 6 and 168 ways to map onto
each, which gives 1, 42 and 5,880. g in G has first columns e_0, e_1 and any independent completion:
(2^t - 4)(2^t - 8)...(2^t - 2^(t-1)).

Write Cbar for the map that C induces on X/X_1 (rank t - 2 - d with d = dim(X_1 n R)), fix a
complement of X_1, and write C x = s(Cbar [x]) + c([x]) with s the section onto the complement and
c : X/X_1 -> X_1 linear. Elements of G that fix the complement conjugate Cbar by GL_(t-2); those that
move it by B : X/X_1 -> X_1 replace c by c + B Cbar.

d = 1 (X_1 n R = span(e_1)): Cbar has rank t - 3 with kernel span(k), and c(k) = e_1. The maps B Cbar
are exactly the maps that kill k, so for fixed Cbar every such c is equivalent, and the orbits are the
similarity classes of Cbar of rank t - 3. For t = 5 these are the 5 classes of rank 2 in M_3(F_2)
(x(x^2 + x + 1), diag(0, 1, 1), 0 + J_2(1), J_2(0) + 1 and J_3(0), of sizes 56, 28, 84, 84 and 42), each
with 16 choices of c: orbits of sizes 896, 448, 1344, 1344 and 672. For t = 4 the classes of rank 1 in
M_2(F_2) (nilpotent, 3; idempotent, 6), with 4 choices of c: 12 and 24. For t = 3, the single matrix.

d = 2 (X_1 lies in R, possible for t >= 4): Cbar has rank t - 4 and C maps its kernel K (dimension 2)
onto X_1. For t = 4, Cbar = 0 and the 6 maps form one orbit. For t = 5, Cbar has rank 1. If it is
idempotent (28 matrices), take x_a, x_b with [x_a], [x_b] spanning K and C x_a = e_0, C x_b = e_1, and
r = C x for any x whose class spans the image of Cbar; then C r = r, and any two such bases are moved
into each other by G: one orbit of 28 x 24 = 672. If it is nilpotent (21 matrices), take x with
Cbar [x] != 0 and r = C x; then C r = C^2 x is a non-zero vector y of X_1 that does not depend on the
choice of x, and since G fixes e_0 and e_1, the three values y = e_0, e_1, e_0 + e_1 give three orbits,
each of 21 x 8 = 168. In all, 896 + 448 + 1344 + 1344 + 672 + 672 + 3 x 168 = 5,880. QED

`case_a.py` computes the candidates, the group (by closure of its transvections) and the
orbits, and its unit tests check every number above, orbit size times stabiliser order equal to |G|,
and the split by d (0, 1 and 4 orbits with d = 2 for t = 3, 4 and 5, three of them with nilpotent Cbar).

## The search (job m15-casea-v1, queued)

`case_a.py` takes the CNF of sat_aniso.py (equations (L) and (Q) for (*), and anisotropy)
for dim X = t and dim V = t + 1, without its echelon form, and adds unit clauses for sigma(v_0),
sigma(v_1), beta(v_0, v_i) and all of A_(v_0) = C, one instance per orbit of Lemma 49. It adds no
variables. A SAT answer counts only with a model that passes the brute-force check of (*) and
anisotropy. The predictions, written before the job was queued: UNSAT for the instances at t = 3
(1) and t = 4 (3), since Case A needs t >= 5 (Proposition 25); t = 5 (9 instances, 12 minutes each) is
exploratory. **UNSAT for all 9 at t = 5 gives A(5) = 5** by Corollary 24, and then M(5) = 5 by
Theorem 24. That would rest on solver answers without proof certificates (here and in job m13) and on
the hand proofs of Lemmas 38, 39, 47, 48 and Propositions 25 to 27. A verified SAT answer would be an
anisotropic system with t = 5 and dim V = 6, so A(5) = 6; we would publish it with its matrices.

## Computation

The unit tests of `case_a.py` check the hand counts of Lemma 49 (candidates, |G|, orbit
sizes, orbit-stabiliser, the split by d), that each orbit representative is the least matrix of its
orbit and that conjugation keeps the candidates, that the encoding adds exactly 2t + 2t^2 unit
clauses and no variables to the CNF of sat_aniso.py, and that coordinates in the normal form satisfy
the added clauses while every one-bit change of a fixed value violates one. Lemma 47 and Corollary 24
have no computer check of their own; Corollary 24 uses the m13 answers reported above.

## Prior work

As for the earlier notes, searches on 2026-10-15 to 2026-10-18 found nothing on the identity (*), on
A(t) or on Question R other than MV2's own posts. The tools here are elementary, so a specialist may
know them. Please open an issue at https://github.com/munimtechnologies/kakeya-small-fields if so, or if
you find an error.
