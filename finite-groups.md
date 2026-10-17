# Cube translates in finite groups: partial families, and 2-groups with central involutions

By MV2 of Munim, Inc. Part of kakeya-small-fields version 1.7.8, 2026-10-17. This file holds
sections 13 and 14 of the README (https://github.com/munimtechnologies/kakeya-small-fields). It
was researched and written with AI agents working in MV2's name. Every statement is proved below,
and most are also checked by exact finite computations (the table at the end says which). **No
human mathematician has checked these proofs.** If you find an error, or find that a result is
already known, please open an issue. Text CC BY 4.0, code Apache-2.0.

Numbering continues from the README: version 1.6 ends with Proposition 4, Lemma 6, Theorem 8 and
Corollary 8, so this file starts at Theorem 9, Lemma 7, Proposition 5 and Corollary 9.

Version 1.7.8 reports the full runs of `cube_groups/m3_core.py` and `cube_groups/m3_exact.py`
(every graded prediction matched) and adds Lemmas 27 and 28 and Corollary 15. If the maps A_h of a
system share an invariant subspace, the system splits into two smaller ones (Lemma 27); if they all
map a hyperplane into a line outside it, an anisotropic system has dim V <= t (Lemma 28). So at
the least t where A(t) = t fails, a counterexample needs an irreducible space of singular
matrices, and the first open case (8, 2) now needs only the irreducible spaces of matrices of rank
<= 2 in M_5(F_2) that are not of Lemma 28's form.
Version 1.7.7 determines M(3) = 3 and extends the answer to the question of section 14 to every
Z_4^a x Z_2^b with b <= 1 or a <= max(7, b + 2). The new tool is Lemma 26: at a zero u of sigma,
the subspace where beta(., u) vanishes carries a smaller system, with values in ker A_u. With it,
Theorem 24 bounds M(t) by the largest anisotropic systems: M(t) <= 2t for every t, and M(3) = 3
with the computation of Proposition 21. Proposition 22 bounds the anisotropic systems for t = 4
and 5, and Corollary 14 counts the cases. This settles (6, 2) and (5, 3), the cases left open in
1.7.6, and every a <= 7. Theorem 23 and its search are superseded but remain true.
Version 1.7.6 corrected section 14. The normal-form conjecture stated after Lemma 23 in version
1.7.5 is false: Example 1 is a system with t = 3 that has no normal form. It was found by hand and
confirmed by `cube_groups/nf_pencil.py`, and Lemma 24 gives an exact criterion for the normal form.
Version 1.7.6 also added Lemma 25, Proposition 21 (a computation: with t = 3, every system on a
space of dimension 4 has a non-zero zero) and Theorem 23 (3 <= M(3) <= 7). Version 1.7.5 added
Lemmas 21 to 23 and Proposition 20. They reduce what is left of the Z_4^a x Z_2^b family to one
question of linear algebra over F_2, about the number M(t) defined before Lemma 21: M(t) <= t + 1
for every t would settle the whole family. Version 1.7.4 added Lemma 20, Theorem 22 and
Corollary 13 (the answer is yes for every Z_4^a x Z_2^b with a <= 4 (every b), b <= 1 or
(a, b) = (5, 2)). Version 1.7.3 added Lemmas 18 and 19, Theorem 21 and Corollary 12 (one argument
for every action of large rank, which settled a <= 3 for every b). Version 1.7.2 added Lemma 17,
Proposition 19 and Theorem 20 (Z_4^3 x Z_2^3), and version 1.7.1 added Lemmas 15 and 16,
Propositions 17 and 18 and Theorem 19 (Z_4^4 x Z_2^2). README sections 14 and 15 still describe
1.7; where they differ, this file is the current statement.

## 13. Cubes for part of the tuples: abelian versus non-abelian groups (new in 1.7)

Section 12 asks a set K to contain a translate of the cube of EVERY r-tuple of G^r. Here K
only has to serve a family D of r-tuples, and we ask how small K can be in terms of |D|. Write

    Y_t = A d_1^(t_1) d_2^(t_2) ... d_r^(t_r)     (t in {0,1}^r),

and say K *serves* d = (d_1, ..., d_r) if some left translate {A w_t(d) : t in {0,1}^r} lies in K.
Logarithms are base 2, H is Shannon entropy, and

    e_r = (1 - 2^(-r)) / r       (e_1 = 1/2, e_2 = 3/8, e_3 = 7/24, e_4 = 15/64).

G' is the derived subgroup, Z(G) the centre, and b(G) the largest conjugacy class size. Since
x^G lies in x G', b(G) <= |G'|. In abelian groups the answer is |K| >= |D|^(e_r) (Theorem 9). In
non-abelian groups this can fail, and the loss can be measured exactly (Theorems 10 to 13). For
D = G^r, the abelian and non-abelian answers agree (Theorem 8).

### A. Abelian groups

**Theorem 9.** Let G be a finite abelian group, r >= 1, d any random element of G^r and A any random
element of G (with any joint law), and Y_t = A + t_1 d_1 + ... + t_r d_r. Then

    sum over t of H(Y_t) >= ((2^r - 1)/r) H(d).

**Corollary 9.** If K contains a translate of the cube of every d in D, then |K| >= |D|^(e_r). With
|D| = delta N^r this is |K| >= delta^(e_r) N^(1 - 2^(-r)).

*Proof.* Step 1 (peeling in any order sigma): sum_t H(Y_t) >= sum_i 2^(i-1) H(d_sigma(i) |
d_sigma(i+1), ..., d_sigma(r)). To see this, peel j = sigma(r) first: the pairs (t, t + e_j) give
H(d_j) + H(Y_t | d_j), and then induct on the face t_j = 0 given d_j. Step 2: the right-hand side
equals H(d) + sum_(i=2..r) 2^(i-2) H(d_(S_i)) with S_i = {sigma(i), ..., sigma(r)}. Step 3: average
over sigma. Han's inequality gives E H(d_(S_i)) >= (|S_i|/r) H(d), and
r + sum_(j=0..r-2) 2^j (r - 1 - j) = 2^r - 1. For the corollary, take d uniform on D; every Y_t
lies in K. QED

Sharpness: equality holds for d uniform on G^r. D = H^r for a subgroup H shows that the exponent of
|D| is best possible, and D = {0} shows that the power of delta is best possible. The Kakeya form
over F_2: a set containing a translate of every subspace in a family F of r-dimensional subspaces
has at least (|F| |GL_r(F_2)|)^(e_r) points.

### B. Every finite group: the counting bound

**Proposition 5.** (a) In every finite group, if K serves every d in D then |D| <= |K|^(r+1), so
|K| >= |D|^(1/(r+1)). (b) This is sharp up to a factor 2: in G = AGL(1, q) = {x -> a x + b},
with H = {x -> a x} and K = H u tH (t: x -> x + 1), |K| = 2(q - 1) and K serves D = G x H^(r-1),
so |D| = q (q - 1)^r.

*Proof.* (a) d -> (A, A d_1, A d_1 d_2, ..., A d_1 ... d_r) maps D one-to-one into K^(r+1), since
d_i is the quotient of consecutive entries. (b) KH = K. Also K^(-1) K = G: given (u, v), if v = 0
take b = e = 0 and c = a u; if v != 0 take b = 0, e = 1, a = 1/v and c = u/v. So for
d = (g, h_2, ..., h_r) pick k, k' in K with k^(-1) k' = g and put A = k. QED

So Theorem 9 fails in AGL(1, q). The failure condition is 2^(r 2^r) (q - 1)^r < q^(2^r - 1), and the
least primes where it holds are q = 257 (r = 2), 67 (r = 3), 59 (r = 4), 73 (r = 5) and 107 (r = 6).
For example, at q = 257, |K| = 512 < |D|^(3/8) = 512.75.

| r | abelian groups (Theorem 9) | every finite group (Proposition 5) |
|---|---|---|
| 1 | 1/2 | 1/2 |
| 2 | 3/8 = 0.375 | 1/3 |
| 3 | 7/24 = 0.2917 | 1/4 |
| 4 | 15/64 = 0.2344 | 1/5 |

### C. Nilpotent groups also fall below the abelian exponent

**Proposition 6.** (a) Let L <= G, y in G with yLy^(-1) != L, and I = L n yLy^(-1). Then K = L u yL
serves D = LyL x L^(r-1), with |K| = 2|L| and |D| = |L|^(r+1)/|I|.
(b) (Class 2.) Let G(p, k) be the set of triples (e, h, z), with e in Z_p and h, z in F_p^k, under
(e, h, z)(e', h', z') = (e + e', h + h', z + z' + e h'). This group has order p^(2k+1), its centre
equals G' = {(0, 0, z)}, and so it has class 2 (G(2, 1) = D_4). Let H = {(0, h, 0)}, choose S in Z_p
with S - S = Z_p (|S| = 2 for p = 2, 3; 3 for p = 5, 7), and let K = {(t, h, t h) : t in S}. Then K
serves D = (G minus HZ) x H^(r-1), with |K| = |S| p^k and |D| = (p - 1) p^(k(r+1)).
(c) (Direct powers.) In G^m take L^m and the diagonal y. With lambda = log|I| / log|L|, the abelian
bound fails for large m if and only if lambda < t_r := (2^r - 1 - r)/(2^r - 1)
(t_2 = 1/3, t_3 = 4/7, t_4 = 11/15).

*Proof.* (a) Write d_1 = l y l' with l, l' in L and take A = l^(-1). Then A d_1 = y l' is in yL, and
every cube point is A h or A d_1 h with h in L. Also |LyL| = |L|^2/|I|. (b) KH = K, and
(t, h, th)^(-1)(t', h', t'h') = (t' - t, h' - h, (t' - t) h'), so K^(-1) K contains every (j, *, *)
with j != 0. (c) |K| = 2|L|^m and |D| = (|L|^(r+1)/|I|)^m, so |K| / |D|^(e_r) -> 0 if and only if
e_r (r + 1 - lambda) > 1. QED

In (b), Theorem 9 asks for |S|^(r 2^r) >= (p - 1)^(2^r - 1) p^(k(2^r - r - 1)), which fails for large
k. The least k where it fails:

    r = 2: k = 9, 4, 3, 2 for p = 2, 3, 5, 7      (p = 7, k = 2: |K| = 147 < |D|^(3/8) ~ 156.0)
    r = 3: k = 7, 3, 3, 2 for p = 2, 3, 5, 7      (3^7 = 2187 is the smallest group in the family)
    r = 4: k = 6 for p = 2

For fixed p, |K| ~ |S| |D|^(1/(r+1)) in this family, so the exponent 1/(r+1) of Proposition 5
is reached up to a constant in nilpotent groups too. In (c), S_3 with L = <(12)> and y = (13) has
lambda = 0 and fails for r = 2 from S_3^9 on.

**Corollary 10.** For a finite group G the following are equivalent: (i) G is abelian; (ii) for
every r and m, all K, D in G^m satisfy |K| >= |D|^(e_r); (iii) for every r there is a C_r > 0 such
that all K, D in every G^m satisfy |K| >= C_r |D|^(e_r).

*Proof.* (i) => (ii) is Theorem 9, and (ii) => (iii) is trivial. For (iii) => (i), suppose G is not
abelian. A non-abelian Dedekind group is Q_8 x E x A, and its square contains Q_8 x Q_8, where
<(i, j)> is not normal; so G or G^2 has a non-normal subgroup L, and then lambda < 1. Choose r with
t_r > lambda and apply Proposition 6(c). QED

### D. How much non-commutativity costs

The proof of Theorem 9 pairs Y_t with Y_(t + e_j). In a non-abelian group the partner is
Y_t c, where c = s^(-1) d_j s is the conjugate of d_j by the product s of the later factors that
are "on". Such a pair is exact when [d_j, s] = 1 and otherwise loses a little. For an index j, a set T
of indices > j and a tuple d, put s_T = prod_(i in T) d_i (in increasing order) and
c_(j,T) = s_T^(-1) d_j s_T. The **fibre count** of a family D is

    beta_(j,T)(D) = max over c of |{d_j : d in D, c_(j,T)(d) = c}|.

Given c, the map d_j -> [d_j, s_T] = d_j^(-1) c is one-to-one, and d_j lies in the conjugacy class
of c. So

    beta_(j,T) <= min( |{[d_j, s_T] : d in D}|, |pi_j(D)| ) <= b(G) <= |G'|.

Multiplying G by an abelian group (and D by any family there) does not change beta.

**Theorem 10 (peeling with fibre losses).** For every finite group G, every random (A, d) and every
order sigma of {1, ..., r},

    sum_t H(Y_t) >= H(A, d) + sum_(m<r) (2^(r-m) - 1) H(x_m | x_1, ..., x_(m-1))
                    - sum over the lossy pairs of H(d_j | c_(j,T)),

where x_m = d_(sigma(m)) is the m-th generator peeled. A pair is lossy when j is peeled while some
unpeeled i > j is on (T is the set of those i). For r = 3 the orders 321, 312, 231, 213, 132 and 123
have 0, 1, 2, 3, 3 and 4 lossy pairs. Here "321" peels d_3 first and is lossless.

*Proof.* At a stage conditioned on the generators F already peeled, a pair (Y, Yc) satisfies
H(Y|F) + H(Yc|F) >= H(Y, c|F) >= H(Y, d_j|F) - H(d_j | Y, c, F) >= H(Y, d_j|F) - H(d_j | c), and
H(Y, d_j|F) = H(d_j|F) + H(Y | d_j, F) is the lossless term. Continue on the face t_j = 0 given
(F, d_j). The last step gives H(A, x_r | x_1..x_(r-1)), so the total starts with H(A, d). QED

With d uniform on D, H(d_j | c_(j,T)) <= log beta_(j,T). Bounding every loss by log|G'| gives the
crude form |K| >= (|D|^(1/r)/|G'|)^(1 - 2^(-r)).

**Lemma 7 (the cube is two-sided).** Put w_i = A d_i A^(-1). Then A d_1^(t_1) ... d_r^(t_r) =
w_1^(t_1) ... w_r^(t_r) A, so flipping t_r is right multiplication by d_r and flipping t_1 is left
multiplication by w_1. Peeling "outside in" (at each step either the last remaining d on the
right or the first remaining w on the left) loses nothing. For every random (A, d) in every finite
group,

    sum_t H(Y_t) >= H(A, d) + sum_(i=1..r-1) (2^(r-i) - 1) H(x_i | x_1, ..., x_(i-1))

for each of the 2^(r-1) outside-in sequences x. For r = 2 this reads
sum >= H(A, d) + max(H(d_2), H(w_1)). *Proof.* All faces used contain the base point, so the word
stays valid. The last pair gives H(A, x_r | x_<r), and (A, x_1, ..., x_r) determines (A, d). QED

**Theorem 11 (r = 2).** For every finite group G and random (A, d_1, d_2), with c = d_2^(-1) d_1 d_2,

    sum_t H(Y_t) >= H(d) + max( H(d_2), H(d_1) - H(d_1 | c) ) >= (3/2) H(d) - (1/2) H(d_1 | c).

So if K serves every pair in D, then

    |K|^8 beta_(1,2)(D) >= |D|^3,   and in particular   |K|^8 b(G) >= |D|^3,   |K|^8 |G'| >= |D|^3.

The exponent 1/8 of the loss cannot be lowered: in G(p, k) (Proposition 6(b)) with b = |G'| = p^k,
|K| / (|D|^(3/8) |G'|^(-1/8)) = |S| / (p - 1)^(3/8) for every k (exactly 2 for p = 2). In AGL(1, q),
b = |G'| = q and the ratio tends to 2.

*Proof.* Theorem 10 with the orders 21 (lossless: H(d) + H(d_2)) and 12 (one lossy pair, which loses
H(d_1 | c)). Average the two and use H(d_1) + H(d_2) >= H(d). A second proof uses Lemma 7:
H(w_1) >= H(d_1) - log b, because d_1 = A^(-1) w_1 A is conjugate to w_1. QED

**Theorem 12 (r = 3).** For every finite group G,

    |K|^24  beta_(1,2) beta_(1,3)^2 beta_(1,23) beta_(2,3)^2  >=  |D|^7,

so |K|^24 b(G)^6 >= |D|^7, i.e. |K| >= |D|^(7/24) b(G)^(-1/4). Within "mix peeling orders and
charge each lossy pair at most log b", the loss exponent 1/4 is optimal.

*Proof.* Average the orders 321, 213 and 132 with weight 1/3 each. They form a Latin square: each
index appears once in each position. Weighted Shearer gives a main term of (7/3) H(d). The losses are
2 H(d_2|c_(2,3)) + H(d_1|c_(1,3)) for 213 and H(d_1|c_(1,2)) + H(d_1|c_(1,3)) + H(d_1|c_(1,23)) for
132. Optimality is a linear program over the six orders. Shearer's main term for all laws needs
coverage 3 p_i + q_i = 4/3 for each index, and the dual vector y = (15/14, 9/14, -3/14) satisfies
3 y_(s1) + y_(s2) <= L(sigma) for all six orders, with value 2. QED

General r: the same LP gives the least average number lam_r of lossy pairs, so
|K| >= |D|^(e_r) b(G)^(-lam_r / 2^r). Solved exactly with dual certificates:

| r | lam_r | loss exponent lam_r / 2^r | uniform order l_r / 2^r | lower limit (r+1) e_r - 1 |
|---|---|---|---|---|
| 2 | 1/2 | 1/8 | 1/8 | 1/8 |
| 3 | 2 | 1/4 | 13/48 | 1/6 |
| 4 | 23/4 | 23/64 | 77/192 | 11/64 |
| 5 | 72/5 | 9/20 | 973/1920 | 13/80 |
| 6 | 67/2 | 67/128 | 2263/3840 | 19/128 |
| 7 | 522/7 | 261/448 | 35101/53760 | 15/112 |

Here l_r = 2^r - 1 - sum_(k=1..r) (2^k - 1)/k is the uniform average over orders. For a uniform
order the Lehmer-code entries X_j are independent and uniform on {0..j-1}, so E 2^(X_j) =
(2^j - 1)/j. The last column comes from Theorem 13's examples: no bound with a smaller loss
exponent can hold.

**Theorem 13 (when the later generators commute).** If d_2, ..., d_r commute pairwise for every d
in D, then

    sum_t H(Y_t) >= ((2^r - 1)/r) H(d) - ((2^r - 1 - r)/r) log b(G),

so |K| >= |D|^(e_r) b(G)^(-((r+1) e_r - 1)). For r = 3 this is |K|^24 b^4 >= |D|^7 (exponent 1/6).
The exponent (r+1) e_r - 1 is sharp for every r: in G(p, k) with D as in Proposition 6(b),
|K| / bound = |S| / (p - 1)^(e_r) for every k. In AGL(1, q) with D = G x H^(r-1), the ratio tends
to 2.

*Proof.* Only pairs that peel d_1 can lose. If d_1 is peeled at position pos, there are
2^(r - pos) - 1 of them. Averaging over all r! orders (pos is uniform) gives (2^r - 1 - r)/r lossy
pairs. The main term is Han's inequality as in Theorem 9. QED

In G(p, k) every order's inequality is tight, and every pair whose commutator can be non-trivial
loses the full log|G'|. For r = 3 the excesses over 8 log|K| are (0, k, 0, k, 3k, 3k) for
(321, 312, 231, 213, 132, 123), in units of log p. So losses cannot be charged per distinct
commutator. In order 132 the three stage-1 pairs lose k each, although the two commutators
[d_1, d_2] and [d_1, d_3] carry only 2k together.

**Proposition 7 (coset designs).** Let L be any subgroup, K = S L a union of |S| left cosets, and D
a subset of (K^(-1) K) x L^(r-1). Every such d is served. Then
|K|^(r 2^r) b(G)^(2^r - 1 - r) >= |D|^(2^r - 1). Since G(p, k) and AGL(1, q) are coset designs,
this is sharp.

*Proof.* For l in L, l g L = (l g l^(-1)) L, so L g L is a union of at most |g^G| <= b left L-cosets,
and |L g L| <= |L| min(|L|, b). So |D| <= |S|^2 |L|^r m with m = min(|L|, b), and
m^(2^r - 1) <= |L|^r b^(2^r - 1 - r). QED

**Proposition 8 (b(G) is sharp where |G'| is not).** Let Gamma(p; j, k) be F_p^j x F_p^k x
(F_p^j (x) F_p^k) with (e, h, z)(e', h', z') = (e + e', h + h', z + z' + e (x) h'). Then
|G'| = p^(jk) and b = p^(j+k-1). For j = 2, S = {0, e_1, e_2}, H = {(0, h, 0)},
K = {(t, h, t (x) h) : t in S} and D = (K^(-1) K) x H^(r-1), we get |K| = 3 p^k and
|K^(-1) K| = (|S - S| - 1) p^(2k) + p^k. K^(-1) K generates G. As k grows (p fixed), Theorem 11 and
Theorem 13 (r = 3) in the b form are tight up to a constant, while the |G'| forms are off by
p^(k-1) and p^(4(k-1)). The abelian r = 2 bound itself fails here once p = 2 and k >= 8, or k = 1
and p >= 31.

**Proposition 9 (the fibre count is the right loss, b is not).** In Gamma(p; j, k) with
S = {0, e_1, ..., e_j} and D = (K^(-1) K) x H^(r-1): |K| = (j+1) p^k, beta_(1,2) = p^k,
|{[d_1, d_2]}| = (j(j+1)/2)(p^k - 1) + 1 (p = 2), b = p^(j+k-1) and |G'| = p^(jk). With j = k, the
abelian r = 2 bound fails by a factor Theta(p^k / k^2). The fibre form allows exactly p^k, which is
tight up to O((log beta)^2). The class-size form allows p^(2k-1), about the square. The smallest
genuine case found is Gamma(3; 4, 4), of order 3^24: |K| = 405, |K^(-1) K| = 131,301,
|D| = 10,635,381. The log2 slacks of |K|^8 m >= |D|^3 are -0.73 for the abelian bound (FAILS), +5.61
with m = beta = 81, +8.91 with the commutator count 801, +10.36 with b = 2187 and +24.6 with
|G'| = 3^16.

### E. The open window for r = 3

For r = 3 the best possible loss exponent lies in [1/6, 1/4]: 1/6 from Theorem 13's examples, 1/4
from Theorem 12. The following results say what an example beating 1/6 would have to look like.

**Proposition 10 (the peeling LP has a unique extremal profile).** For product laws, cap each
[d_1, .]-pair loss at g = log b and each [d_2, d_3]-pair loss at lambda g (0 <= lambda <= 1). Then
peeling proves at best a loss exponent of 1/6 + lambda/12. For lambda > 0 this is attained only at
H(d_1) - H(d_2) = (1 - 4 lambda/7) g and H(d_1) - H(d_3) = (1 + 2 lambda/7) g, where the
orders 321, 213 and 132 are tight. *Proof.* The six constraints are linear in (E, x, y). The only
dual solution is the Latin square (1/3, 1/3, 1/3), with value 4 + 2 lambda. QED
So an example beating 1/6 needs d_1 freest, d_2 richer than d_3 by about (6 lambda / 7) g, and
[d_2, d_3] carrying entropy: d_2 and d_3 cannot come from the same set.

**Proposition 11 (normal one-sided designs lose nothing).** Let L be a normal subgroup with K L = K
and j in {1..r}. If every d in D has d_j in L, then |D| <= |K|^r, so |K| >= |D|^(1/r) > |D|^(e_r).
*Proof.* In G/L, A-bar and A-bar d-bar_i (i != j) lie in K/L. Each d-bar_i has |L| lifts, and d_j
has |L| choices. QED. Normality is needed: in AGL(1, 5) with the non-normal L = H,
K = L u (x -> x + 1) L serves G x L, and |D| = 80 > 64 = |K|^2.

**Lemma 8 (the core can be removed).** If every finite group satisfies |K| >= c |D|^e b^(-eps)
with 0 < e <= 1/r, then passing to G / core(Stab_R(K)) only gains a factor |N|^(1 - r e). So a family
beating a loss exponent may be taken with a right stabiliser that contains no non-trivial normal
subgroup. Both extremal families (AGL(1, q) and G(p, k)) are already of this form:
Stab_R(K) = H, and core(H) = 1.

Recorded so that nobody retries these routes: per-commutator charging (false in G(p, k));
coset designs with any stabiliser, abelian or not (Proposition 7); mixtures of orders (the LP
optimum is exactly 1/4); an absorbed normal generator (Proposition 11); crude two-sided peeling
(Lemma 7 reproduces orders 312 and 132 with the same losses); and searches in small groups (the
abelian bound holds for every K in every group of order <= 24 that we tried, so breaks need
families like Gamma(3; 4, 4)).

### F. Powers of a group: the single-subgroup exponent

By Proposition 6(c), the powers of G break the abelian exponent through one subgroup exactly when
some lambda = log|L n yLy^(-1)| / log|L| is below t_r. Let lambda*(G) be the infimum over m, over
L != 1 in G^m and over y.

**Proposition 12 (lambda* is the central density).**
lambda*(G) = inf over m and L != 1 in G^m of log|L n Z(G)^m| / log|L|.
*Proof.* Central elements of L lie in every conjugate, which gives >=. For <=, let g_1..g_d generate
G^m. Take the diagonal L' of L in (G^m)^(d+1) and y = (1, g_1, ..., g_d). Then L' n yL'y^(-1) is
the diagonal of L n Z(G^m). QED

**Lemma 9.** Let G have class <= 2, let G' have exponent p, and let every element of order p be
central. Then every subgroup L of G satisfies |L n Z|^3 >= |L| (p = 2) and |L n Z|^2 >= |L|
(p odd). These hypotheses pass to G^m x A with A abelian. Examples: Q_8^m x A, Q_8 x Z_2,
Z_4 x| Z_4 and P(p) below. *Proof.* Put N = L n Z. For odd p, x -> x^p is a homomorphism
L -> N whose kernel is central. For p = 2, Q(xN) = x^2 N^2 is a quadratic map L/N -> N/N^2 with no
non-trivial zero, so Chevalley-Warning gives dim(L/N) <= 2 dim(N/N^2). QED

So lambda*(G) >= 1/3 (p = 2) or 1/2 (p odd), and in these groups no single-subgroup design breaks
the r = 2 exponent. Both values are attained. For p = 2, take the diagonal Q_8 in Q_8^3 with
y = (i, j, 1) (Proposition 13). For p odd, take P(p) = {(a, b, c) : a, b mod p^2, c mod p} with
(a, b, c)(a', b', c') = (a + a', b + b', c + c' + b a'), of order p^5, with L = {(k, 0, 0)} and
y = (0, 1, 0), so that |L| = p^2 and |I| = p. Powers of P(p) break r = 3 (from P(3)^16, P(5)^11 and
P(7)^9 on) but never r = 2.

**Proposition 13 (powers of Q_8).** In Q_8^3, the diagonal L = {(x, x, x)} with y = (i, j, 1) has
|I| = 2 = |L|^(1/3). For r = 2 the designs in (Q_8^3)^m stay exactly a factor 2 above the abelian
bound. For r = 3 they break it from Q_8^15 on (|K| = 2^16, |D| = 2^55, 384 < 385), and for
r = 4, 5, 6 from Q_8^12 on.

**Proposition 14 (Q_8^m-type groups, r = 2).** Let G satisfy Lemma 9 with p = 2 (for example
Q_8^m x A). (a) For subgroups L_1 and L_2 and K = L_1 u yL_2, the vertex pattern
(Y_00, Y_01 in L_1; Y_10, Y_11 in yL_2) serves D_P = (L_1 y L_2) x (L_1 n L_2), with
|D_P|^(3/8) <= max(|L_1|, |L_2|) < |K|. (b) If K = S L is a union of left cosets and D is
(K^(-1) K) x L, then |K| >= |S|^(1/4) |D|^(3/8). The other 15 vertex patterns of (a), and general D in
(b), are not covered.

**Proposition 15 (which powers break r = 2).** (a) If G has a non-central element x of prime order,
then lambda*(G) = 0, attained in G^2 by L = <(x, x)> and y = (g, 1) with gx != xg. Its powers break
every r >= 2. (b) Groups as in Lemma 9 have lambda* >= 1/3 or 1/2. (c) Abelian groups have
lambda* = 1.

**Corollary 11 (generalised quaternion groups).** Q_(2^n) has a single involution, which is
central, but lambda*(Q_(2^n)) <= 1/n (diagonal of the whole group in Q_(2^n)^3). So powers of Q_16
break the r = 2 exponent (from Q_16^27 on) and the r = 3 exponent (from Q_16^9 on). Lemma 9 needs
class 2.

**Theorem 14 (odd p).** Let p be odd and G a finite p-group of exponent p^e in which every element
of order p is central. Then every subgroup L of every G^m satisfies |L| <= |Omega_1(L)|^e, so
lambda*(G) >= 1/e. This is sharp for every e and p: in M(p, e) = <x, y | x^(p^e) = y^(p^e) = 1,
y x y^(-1) = x^(1+p)>, L = <y> has |I| = p and |L| = p^e.
*Proof.* Xu's theorem (as stated in Guerboussa, arXiv 1404.3621, Lemma 2.10): when
Omega_1(gamma_(p-1)(H)) <= Z(H), (i) the elements of order dividing p^n form a subgroup and
(ii) |H : H^(p^n)| <= |Omega_n(H)|. Every subgroup H of G^m qualifies. H^p has exponent <= p^(e-1),
satisfies the hypothesis, and has Omega_1(H^p) <= Omega_1(H). By (ii) with n = 1,
|H : H^p| <= |Omega_1(H)|. Induct on e. QED
So for odd p, groups of exponent p^2 or p^3 with central elements of order p never break r = 2
through one subgroup. Exponent p^4 does: M(p, 4)^m fails if and only if p^m > 256. The bound
|G| <= |Omega_1(G)|^e is very likely known to specialists (Xu; compare Gonzalez-Sanchez and Weigel,
arXiv 0905.4513, Theorem C). Only its use here is ours. We have not read Xu's paper itself (Bull.
Austral. Math. Soc. 36 (1987) 1-10); statement (ii) is taken from Guerboussa's citation of it.

For p = 2 the analogue is the open question of section 14. Its class-2 case (Theorem 15) gives
lambda*(G) >= 1/(e+1) for class-2 groups whose involutions are all central, sharp for e = 2 by Q_8.
For e >= 3 this is below 1/3, so it only limits how badly r = 2 can break.

*Checks.* Each statement above except Proposition 14, Lemma 8 and the uniqueness claim of
Proposition 10 was checked by an exact finite computation (the table at the end of this file):
the abelian bound for every K in 16 abelian groups (r = 1..4) and on random entropy laws; the
AGL(1, q) and G(p, k) thresholds; Theorems 10 to 13 on random joint laws in S_3, D_4, Q_8, A_4, S_4
and AGL(1, 5) (least slack >= 0) and for every K in S_3, D_4 and Q_8; the G(p, k) excess table; the
order LP for r = 2..7 with dual certificates and vertex enumeration; Propositions 7, 8, 9 and 11
by brute force; Lemma 9, Proposition 12, Theorem 14 and the diagonal examples on every subgroup of
the groups named. Proposition 14, Lemma 8 and Proposition 10's uniqueness claim are proved by hand
only.

*Prior work.* Searches on 2026-10-15 and 2026-10-16 found nothing on sets containing translates of
cubes in non-abelian groups. The nearest work we found is Tao's non-commutative entropy
(arXiv math/0601431) and the work of Gill, Lifshitz, Pyber and Szabo on the Liebeck-Nikolov-Shalev
conjecture about product sets (arXiv 2408.07800). The
arguments are short Shannon-inequality and counting arguments, so a specialist may find them
routine. If any of this is known, please open an issue and we will cite it.

## 14. Appendix: 2-groups whose involutions are all central (new in 1.7)

Theorem 14 bounds a p-group by its elements of order p when p is odd. For p = 2 we ask:

**Question.** Let L be a finite 2-group of exponent 2^e whose involutions are all central, and let
Omega = Omega_1(L), elementary abelian of rank k. Is |L| <= |Omega|^(e+1)?

Equality holds for Q_(2^n) (e = n - 1, k = 1), Q_8^m and Q_8^m x Z_4. The exponent e + 1 cannot be
lowered, because of the generalised quaternion groups. A yes would give lambda*(G) >= 1/(e+1) in
section 13. This section settles the question in several natural families. It does NOT settle
the general case.

**Lemma 10 (second centre).** rank Omega_1(Z_2(L)/Z(L)) <= 2k. *Proof.* On N/Z = Omega_1(Z(L/Z)),
q(xZ) = x^2 Z^2 is a k-tuple of quadratic forms with no non-trivial common zero, and
Chevalley-Warning applies. QED Sharp for Q_8^m.

**Theorem 15 (class 2).** If L has class <= 2 and Z(L) = prod_j (Z_(2^j))^(a_j), then

    log2 |L| <= e k + a_(e-1) <= (e + 1) k.

*Proof.* Let V = L/Z. It has exponent dividing 2^(e-1). Let d_i = rank of V^(2^i) and
M_i = Omega_1(V) n V^(2^i). (1) On N/Z = Omega_1(V), q(xZ) = x^2 Z^2 is quadratic with polar form
[y, x] Z^2, and it has no non-trivial zero. (2) q(M_i) lies in Omega_(e-i-1)(Z) Z^2 / Z^2, of
dimension A_(e-i-1), where A_j = a_1 + ... + a_j. (3) On M_1, q is additive (B(x^2 Z, yZ) =
[y, x]^2 Z^2 = 0) and injective, so d_i <= A_(e-i-1) for i >= 1. (4) q modulo q(M_1) is
anisotropic on a complement of M_1, so d_0 - d_1 <= 2(A_(e-1) - d_1). (5) Add up: the coefficient of
a_j in the bound for log2|L| is e, except for j = e - 1, where it is e + 1. QED
Equality: Q_8^m, Q_8 x Z_4, Q_8 x Z_8 and Q_8^2 x Z_4. Q_16 (class 3, 16 > 2^3) shows that class 2 is
needed for the sharper form. Exponent 4 with central involutions forces class <= 2, so e <= 2 is
settled.

**Proposition 16 (power map a homomorphism).** If x -> x^(2^(e-1)) is a homomorphism, then
|L| <= |Omega| |K_1| with K_1 its kernel. So the answer is yes for e = 3 whenever x -> x^4 is a
homomorphism.

**Lemma 11 (series with unique-involution factors).** If L has a normal series of length s whose
factors each have a unique involution, then |L| <= 2^((e+1) s). (Each factor is cyclic or
generalised quaternion.) The Sylow 2-subgroup of PSU_3(4) (order 64, k = 2) has no such series of
length 2. It still meets the bound, since e = 2.

**Lemma 12 (reduction).** If no element squares into W \ {1} for a subgroup W <= Omega, then the bound
for L/W gives the bound for L. So a minimal counterexample has every involution a square.

**Lemma 13 (the Z_4^k framework).** Let A <| L, A ~ Z_4^k, C_L(A) = A (then Omega = 2A), and
H = L/A. Write A additively and identify A/2A and 2A with F_2^k. (a) g acts as a -> a + M_g(a-bar),
and h -> M_h is an injective additive map H -> M_k(F_2). So H is elementary abelian of rank
n <= k^2, and e <= 3. (b) sigma(h) = g^2 mod 2A is quadratic, with polar form
beta(h, h') = [g, g'] mod 2A. (c) M_(h') sigma(h) = (I + M_h) beta(h, h'). (d) No involution
lies outside A if and only if, for every h != 0, either sigma(h) != 0 or g^2 = 2t with t not in
Im(I + M_h).

**Lemma 14 (a determinant count).** If W <= M_k(F_2) is a subspace and I + M is singular for every
non-zero M in W, then dim W <= k (sharp: diagonal matrices). *Proof.* h -> det(I + M_h) is the
indicator of 0 on W, has degree <= k, and its multilinear form is prod (1 + x_i), of degree dim W.
QED Very likely known. Recorded as a tool.

**Theorem 16 (self-centralising normal Z_4^k).** If L has a self-centralising normal subgroup
A ~ Z_4^k, then |L : A| <= 2^(2k), so |L| <= |Omega|^4 and the answer is yes. In particular the
answer is yes whenever a maximal normal abelian subgroup of L is homocyclic of exponent 4.
*Proof.* Let N_h = I + M_h + D(sigma(h)), where D(s) is the diagonal matrix with diagonal s. If h = 0,
det N_h = 1. If sigma(h) = 0 and h != 0, then I + M_h is singular by Lemma 13(d). If
sigma(h) = s != 0, then M_h s = 0 by 13(c) and D(s) s = s over F_2, so N_h s = 0. Hence
h -> det N_h is the indicator of 0 on F_2^n. Its entries have degree <= 2, so n <= 2k. QED

**Theorem 17 (self-centralising normal Z_4^a x Z_2^b).** Let A <| L, C_L(A) = A, A ~ Z_4^a x Z_2^b,
k = a + b. Write delta_h = [P_h ; Q_h] for the action (P into 2A, Q into a complement of 2A in
Omega). Let H_0 = ker(h -> Q_h), n_0 = dim H_0, and s = dim span sigma(H_0). Then

    n_0 <= a + s + 2b,   n - n_0 = rank Q <= b (a - s),   so   n <= a + 2b + ab - s(b - 1).

So the answer is yes when ab - s(b - 1) <= a + b: in particular when b <= 1 (every a), when a <= 2,
and when b = 2 and s >= a - 2.
*Proof.* (i) The identity delta_(h') sigma(h) = (J + delta_h) beta(h, h') (J = doubling), read in
the Q-rows for h in H_0, shows that every Q_(h') kills span sigma(H_0). (ii) On H_0 the square
rho(h) = g^2 mod 2A is well defined and quadratic. Split it as (sigma, rho_2). Then
F(h) = det(I + P_h + D(sigma(h))) prod_j (1 + rho_2,j(h)) is the indicator of 0 on H_0, by the same
three cases as Theorem 16 plus "rho_2(h) != 0 kills the product". Its degree is <= (a + s) + 2b.
QED (The degree count uses a basis of A in which span sigma(H_0) is spanned by the first s basis
vectors, so that D(sigma(h)) has at most s non-zero entries.)

**Theorem 18 (full rank Q).** In the setting of Theorem 17 let b >= 2 and rank Q = ab, i.e.
Q(H) = Hom(F_2^a, F_2^b). Then beta(H, H_0) = 0, sigma(H_0) = 0, and every P_h with h in H_0 kills
S = span sigma(H). Hence n_0 <= a - dim S + 2b. If S = 0, L has exponent 4. So for b >= 2, always
n <= a + 2b + ab - 1 (or e <= 2), and the answer is yes whenever (a - 1)(b - 1) <= 2. In particular
**(a, b) = (3, 2) is settled for every s.**
*Proof.* Fix h' in H_0, so Q_(h') = 0. The Q-rows of the identity in Theorem 17 give
Q_h l(h) = 0 for all h in H, where l(h) = beta(h, h') is linear. Polarising gives
Q_h l(h'') + Q_(h'') l(h) = 0. For h in H_0 this says that every map in Q(H) = Hom kills l(h), so
l(H_0) = 0 and l(h) = lam(Q_h) for a linear lam : Hom -> F_2^a with M lam(M') + M' lam(M) = 0. Take
M = u v^T of rank 1 and w = lam(M). Then M' w = u (v^T lam(M')) lies in span(u) for every M'. If
w != 0, the values M' w fill F_2^b, which is not inside a line when b >= 2. So lam vanishes on rank-1
maps, which span Hom, and lam = 0. Next, the full identity with h' in H_0 reads
delta_(h') sigma(h) = (J + delta_h) beta(h, h') = 0, so P_(h') kills sigma(h). The Q-rows with h in
H_0 give Q_(h') sigma(h) = 0 for all h', so sigma(H_0) = 0. In a basis whose first dim S vectors
span S, I + P_h (h in H_0) is block triangular with an identity block. So det(I + P_h) has degree
<= a - dim S, and Theorem 17's indicator F has degree <= a - dim S + 2b. If S = 0, every square
lies in Omega, so x^4 = 1. Cases: s >= 1 (Theorem 17: n <= a + 2b + ab - s(b-1) <= a + 2b + ab - 1);
s = 0 with rank Q <= ab - 1; s = 0 with rank Q = ab (above). Each gives n <= a + 2b + ab - 1, and
n <= 2a + 3b is what |L| <= |Omega|^4 needs. QED
The step lam = 0 fails for b = 1 (the symmetric zero-diagonal matrices solve it), so b >= 2 is
needed.

The rest of this section (new in 1.7.1) settles (a, b) = (4, 2). Keep the setting of Theorem 17,
write W = Q(H) and r = dim W = rank Q, and let N(W) be the set of vectors killed by every map in W.
The first step of Theorem 18's proof works for any W: for h' in H_0, l = beta(., h') maps H_0 into
N(W), and modulo N(W) it is lam(Q_h) for a linear lam : W -> F_2^a / N(W) with M lam(M) = 0 for
every M in W. Write Lam(W) for the space of such lam.

**Lemma 15 (a quadratic equation).** Let q be a non-zero quadratic form on an F_2-space V with polar
form B, let u != 0 be a vector, and let p : V -> F_2^a be linear with

    q(h) p(h') = B(h, h') (u + p(h))     for all h, h' in V.

Then p(h') = B(h*, h') u for every h* with q(h*) = 1. Write p = pi u. Then rank B <= 2; if B = 0
then pi = 0; and if B != 0 then q vanishes on rad B.
*Proof.* Put h = h*: p(h') = B(h*, h') (u + p(h*)), and h' = h* gives p(h*) = 0 because B is
alternating. So p = pi u with pi = B(h*, .) for every such h*. Hence q = 1 only on h* + R, where
R = rad B. If B = 0 then pi = 0. Let B != 0. For h outside R with q(h) = 0, choose h' with
B(h, h') = 1; the equation gives pi(h) = 1, that is B(h*, h) = 1. If h* were in R, every h outside
R would have q(h) = 0 (q = 1 only on h* + R = R) and B(h*, h) = 0, which is impossible since B != 0
gives such h. So h* is not in R, and q vanishes on R. If
dim V/R >= 4, the B-orthogonal of h* in V/R has dimension >= 3 and contains a class other than 0
and h* + R; its elements h lie outside R and outside h* + R, so q(h) = 0 and B(h*, h) = 0, a
contradiction. So rank B = dim V/R <= 2. QED

**Lemma 16 (rank-1 maps span a hyperplane).** For C != 0 in Hom(F_2^a, F_2^b), the rank-1 maps in
C^perp = {M : tr(C^T M) = 0} span C^perp.
*Proof.* A D orthogonal to all of them satisfies u^T D v = 0 whenever u^T C v = 0. For each u this
forces D^T u in {0, C^T u}, so F_2^b is the union of the subspaces ker D^T and ker (D + C)^T. One of
them is everything, so D = 0 or D = C. QED

**Proposition 17 (squares in a line).** In the setting of Theorem 17 (any b >= 0), suppose that
S = span sigma(H) has dimension <= 1. Then e <= 2 (if S = 0) or n <= a + 2b + 3. So the answer is
yes whenever dim S <= 1 and a + b >= 3.
*Proof.* If S = 0, every square lies in Omega and x^4 = 1. Let S = span(u), so sigma = q u and
beta = B u for a quadratic form q on H with polar form B. The P-rows of the identity of
Theorem 17 read q(h) P_(h') u = B(h, h') (u + P_h u), so by Lemma 15 (with p(h) = P_h u),
rank B <= 2. Now let X = L/Omega and let u-bar in X be the image of a lift of u. A/Omega is central
in X, and every square and every commutator of X lies in <u-bar>, which is central of order 2. So
X/<u-bar> is elementary abelian of dimension a + n - 1, and squaring defines a quadratic form on it
whose polar form is the commutator, that is B pulled back from H, of rank 2 rho <= 2. Its radical
has a subspace of codimension <= 1 on which the form vanishes, and a complement contains a totally
singular subspace of dimension >= rho - 1, so there is a totally singular subspace T of
dimension >= (a + n - 1) - rho - 2. Its preimage Y-bar in X is elementary abelian of dimension
dim T + 1, and y -> y^2 maps it into Omega: a k-tuple of quadratic forms that vanishes only at 1,
because an element squaring to 1 is an involution, so lies in Omega. Chevalley-Warning gives
dim T + 1 <= 2k, so a + n - rho - 2 <= 2a + 2b and n <= a + 2b + 3. QED

**Proposition 18 (hyperplanes of maps).** Let b >= 2 and let W <= Hom(F_2^a, F_2^b) have
codimension <= 1. Then N(W) = 0 and Lam(W) = 0.
*Proof.* The maps killing a fixed v != 0 have codimension b >= 2, so N(W) = 0. Codimension 0 is
Theorem 18's lemma. Let W = C^perp and lam in Lam(W), so M lam(M) = 0 and
M lam(M') + M' lam(M) = 0 on W. Take M = u v^T of rank 1 in W and w = lam(M). As in Theorem 18,
M' w lies in span(u) for every M' in W. If w != 0, the image of W under M' -> M' w is F_2^b unless
C = z w^T, in which case it is z^perp, of dimension b - 1. So b = 2, C = z w^T and z^T u = 0. Choose
v' with v'^T w = 1 and put M'' = u v'^T, which lies in W. The same argument gives lam(M'') in
{0, w}, and M'' lam(M'') = 0 gives v'^T lam(M'') = 0, so lam(M'') = 0. Then
M lam(M'') + M'' lam(M) = u (v'^T w) = u != 0, a contradiction. So lam vanishes on the rank-1 maps
of W, which span W by Lemma 16. QED
Without the equations M lam(M) = 0 (keeping only the polar ones) this fails exactly when b = 2 and
rank C = 1: if C = z w^T, u_0 is the non-zero vector with z^T u_0 = 0 and y^T u_0 = 1, then
lam(M) = (y^T M w) w solves them.

**Theorem 19 ((a, b) = (4, 2)).** If L has a self-centralising normal subgroup A ~ Z_4^4 x Z_2^2,
then |L| <= |Omega|^4. So the answer is yes, and together with Theorems 17 and 18 it is yes for
every Z_4^a x Z_2^b with a <= 2, b <= 1 or (a - 1)(b - 1) <= 3.
*Proof.* We need n <= 2a + 3b = 14 when e = 3. By Proposition 17 we may take dim S >= 2. Theorem 17
gives n_0 <= 8 + s and r <= 2(4 - s), so n <= 16 - s and s >= 2 is done.
(s = 0.) If r <= 6, n <= 8 + 6. If r >= 7, W has codimension <= 1, so by Proposition 18 the map lam
is 0 for every h' in H_0, that is beta(H, H_0) = 0. As in Theorem 18, every P_(h') with h' in H_0
then kills S, and n_0 <= a - dim S + 2b <= 6, so n <= 6 + 8.
(s = 1.) Let sigma(H_0) span span(u). Then W kills u, so r <= 6, and r <= 5 gives n <= 9 + 5. If
r = 6, W is all of Hom(F_2^4 / span(u), F_2^2) and N(W) = span(u). Theorem 18's lemma for
Hom(F_2^3, F_2^2) gives lam = 0, so beta(h', h) = gamma(h', h) u for h' in H and h in H_0. Write
sigma = q u on H_0, with polar form B = gamma on H_0, and choose a basis of A with u first. The
P-rows of the identity give, for h in H_0 and h' in H,

    q(h) P_(h') u = gamma(h', h) (u + P_h u).

Taking h = h* with q(h*) = 1 shows P_(h') u = pi(h') u for all h' in H, with pi = gamma(., h*), and so
q(h) pi(h') = gamma(h', h) (1 + pi(h)). Restricted to H_0 this is Lemma 15. If B = 0, then
P_h u = 0 on H_0 and q is linear, so the first column of I + P_h + D(sigma(h)) is (1 + q(h)) u.
Its determinant has degree <= 1 + (a - 1) = a, and n_0 <= a + 2b = 8. If B != 0, then rank B = 2,
and q and pi vanish on R = rad B, so the displayed equation gives gamma(H, R) = 0. For h in R this
means beta(H, h) = 0 and sigma(h) = 0, so P_h kills S. Theorem 17's indicator restricted to R then
has degree <= a - dim S + 2b <= 6. So n_0 = dim R + 2 <= 8. In every case n <= 14. QED

The same tools also sharpen Theorem 18: if rank Q = ab, Proposition 17 forces dim S >= 2 (or
n <= a + 2b + 3), so n <= a + 2b + ab - 2. The s = 1 part of the proof uses only b >= 2: for every
such (a, b), s = 1 gives n <= a + b + ab or n <= a + 2b + 3 (with dim S >= 2, n_0 <= a + 2b when
r = b(a - 1), and n_0 <= a + 1 + 2b otherwise). The next open cases after Theorem 19 were
(a, b) = (3, 3) and (5, 2). The rest of this section (new in 1.7.2) settles (3, 3).

**Lemma 17 (squares against images).** In the setting of Theorem 17, for every h in H,

    Q_h sigma(h) = 0     and     Q_(h') sigma(h) lies in Im Q_h for every h' in H.

So if Q(H) = Hom(F_2^a, F_2^b) and a <= b, then sigma = 0 on H and L has exponent 4. (When a > b
it still says that sigma(h) = 0 unless Q_h is onto, and that sigma(h) lies in ker Q_h.)
*Proof.* The Q-rows of the identity of Theorem 17 read Q_(h') sigma(h) = Q_h beta(h, h') for all h
and h' in H. This gives the second claim, and h' = h gives the first, because beta is alternating.
If Q(H) is all of Hom and sigma(h) != 0, the maps Q_(h') send sigma(h) to every vector of F_2^b, so
Q_h is onto. No map is onto when a < b. When a = b, Q_h is then invertible and Q_h sigma(h) = 0
forces sigma(h) = 0. With sigma = 0 every square lies in Omega, so x^4 = 1, as in Theorem 18. QED
So for a <= b the remark above improves: rank Q = ab gives e <= 2. The identity used here is
checked on every pair h, h' of ten explicit groups by `cube_groups/z4z2.py`.

**Proposition 19 (subspaces of small codimension).** Let b >= 2 and let W <= Hom(F_2^a, F_2^b) have
codimension c <= b - 1. Then N(W) = 0 and Lam(W) = 0. This contains Proposition 18 (b = 2) and the
lemma in Theorem 18 (c = 0), and its proof does not need Lemma 16.
*Proof.* (1) For v != 0 in F_2^a, the vectors u in F_2^b with u v^T in W satisfy c < b linear
equations, so some u != 0 does. So a vector killed by every rank-1 map of W is orthogonal to every
v, hence 0. In particular N(W) = 0.
(2) Let lam be in Lam(W), let M = u v^T be a rank-1 map in W, and w = lam(M). The polar equations
give M' w = M lam(M') = u (v^T lam(M')), which lies in span(u), for every M' in W. The map
M' -> M' w sends Hom onto F_2^b, and its kernel K_w = {M' : M' w = 0} has codimension b. So if
w != 0, the image of W has dimension >= b - c >= 1. Since it lies in span(u), it is span(u), c = b - 1,
K_w lies in W, and W = {M' : M' w in span(u)}. Then M w = 0 gives v^T w = 0. Choose v' with
v'^T w = 1; then M'' = u v'^T lies in W. If w'' = lam(M'') were non-zero, the same argument would put
K_(w'') inside W. That forces w'' = w: otherwise some M' kills w'' and sends w outside span(u),
since b >= 2. But M'' w = u != 0, while M'' lam(M'') = 0. So lam(M'') = 0, and the polar equation for
M and M'' reads 0 = M lam(M'') + M'' lam(M) = u, a contradiction. Hence lam vanishes on every rank-1
map of W.
(3) For M in W and a rank-1 map M' in W, M' lam(M) = M lam(M') + M' lam(M) = 0. So lam(M) is
killed by every rank-1 map of W, and lam(M) = 0 by (1). QED
Both hypotheses are needed. At c = b, the 2^a - 1 subspaces K_w have N(K_w) = span(w). At c = b - 1,
on each of the (2^a - 1)(2^b - 1) subspaces W = {M : M w in span(u)}, the polar equations alone are
solved by lam(M) = (y^T M w) w with y^T u = 1. So the diagonal equations M lam(M) = 0 are needed,
as after Proposition 18. (The full run of case33.py also found that on every other W of
codimension b - 1 the polar equations alone already force lam = 0, for all nine pairs (a, b) it
checks, up to (3, 3) and (2, 4).)

**Theorem 20 ((a, b) = (3, 3)).** If L has a self-centralising normal subgroup A ~ Z_4^3 x Z_2^3,
then |L| <= |Omega|^4. So the answer is yes for every Z_4^a x Z_2^b with a <= 2, b <= 1,
(a - 1)(b - 1) <= 3 or (a, b) = (3, 3).
*Proof.* We need n <= 2a + 3b = 15 when e = 3. By Proposition 17 we may take dim S >= 2. Theorem 17
gives n_0 <= 9 + s and r <= 3(3 - s), so n <= 18 - 2s, and s >= 2 is done. For s = 1 the remark
after Theorem 19 gives n <= a + b + ab = 15. Let s = 0. If r <= 6, then n <= 9 + 6. If r = 9,
Lemma 17 (a = b) gives S = 0, which we have excluded. If r = 7 or 8, W has codimension <= 2 = b - 1,
so N(W) = 0 and Lam(W) = 0 by Proposition 19, and the step before Lemma 15 gives beta(H, H_0) = 0.
As in Theorem 18, every P_(h') with h' in H_0 then kills S, and n_0 <= a - dim S + 2b <= 7. So
n <= 7 + 8 = 15. QED

The rest of this section (new in 1.7.3) replaces the case analyses of Theorems 18 to 20 by one
argument for every W of large dimension, and settles a = 3 for every b. Keep the setting of
Theorem 17, with W = Q(H), r = dim W, S = span sigma(H), and for y != 0 in F_2^b put

    V_y = {x in F_2^a : y^T M x = 0 for every M in W},     d_y = dim V_y.

**Lemma 18 (subspaces where sigma vanishes).** If T <= H is a subspace with sigma(T) = 0, then
dim T <= a + 2b.
*Proof.* Let Y be the preimage of T in L. Since beta is the polar form of sigma, beta(T, T) = 0. So
Y/Omega is generated by the central subgroup A/Omega of L/Omega and by elements whose squares and
commutators lie in Omega: it is elementary abelian of dimension a + dim T. Omega is central of
exponent 2, so y -> y^2 is a well-defined map from Y/Omega to Omega, and
(yz)^2 = y^2 z^2 [z, y] with [z, y] in Omega bilinear. So it is a k-tuple of quadratic forms in
a + dim T variables. It vanishes only at the identity, because an element with y^2 = 1 is an
involution and lies in Omega. Chevalley-Warning gives a + dim T <= 2k = 2a + 2b. QED
This is the last step of the proof of Proposition 17, stated on its own.

**Lemma 19 (slices).** Let W <= Hom(F_2^a, F_2^b). For every basis y_1, ..., y_b of F_2^b,

    d_(y_1) + ... + d_(y_b) <= codim W.

So if codim W < 2b (that is, r >= b(a - 2) + 1), some y has d_y <= 1. This is sharp: at
codim W = 2b, every d_y >= 2 exactly when W = K_X = {M : M X = 0} with dim X = 2, and then every
d_y = 2.
*Proof.* Pair Hom(F_2^a, F_2^b) with F_2^a (x) F_2^b by <M, x (x) y> = y^T M x. Then
V_y (x) y = W^perp n (F_2^a (x) y), where W^perp has dimension codim W. For a basis y_i these
pieces are independent: if sum x_i (x) y_i = 0, read it as the a x b matrix sum x_i y_i^T and
multiply by w_j with y_i^T w_j = 1 if i = j and 0 otherwise; this gives x_j = 0. For sharpness, if
codim W = 2b and every d_y >= 2, then W^perp is the direct sum of the X_i (x) y_i with
X_i = V_(y_i) of dimension 2. An element of W^perp in F_2^a (x) (y_i + y_j) has the form
x (x) (y_i + y_j) with x in X_i n X_j, so V_(y_i + y_j) = X_i n X_j has dimension 2 only if
X_i = X_j. So all X_i are one X, W^perp = X (x) F_2^b and W = K_X. QED

**Theorem 21 (large rank).** In the setting of Theorem 17, suppose that some y != 0 has
dim(V_y n S) <= 1. Then n <= 2a + 2b + 1, and n <= 2a + 2b - d_y if V_y n S = 0. So
|L| <= |Omega|^4 when b >= 1. By Lemma 19 this applies whenever r >= b(a - 2) + 1. In particular,
if Q has full rank then every V_y = 0 and n <= 2a + 2b, for every a and every b >= 1.
*Proof.* Let U_y = {M in W : y^T M = 0} and T_y = {h in H : Q_h in U_y}, a subspace containing H_0.
The map W -> (F_2^a)*, M -> y^T M, has image the annihilator of V_y, so dim U_y = r - a + d_y and
dim T_y = n - a + d_y. For h in T_y, Lemma 17 puts every Q_(h') sigma(h) in Im Q_h, which lies in
ker y^T. So y^T M sigma(h) = 0 for every M in W, that is sigma(h) is in V_y, and
sigma(T_y) <= V_y n S. If V_y n S = 0, Lemma 18 gives n - a + d_y <= a + 2b. Otherwise
V_y n S = span(v); write sigma = q v on T_y, with q a quadratic form with polar form B, so that
beta = B v on T_y. For h and h' in T_y the P-rows of the identity of Theorem 17 read

    q(h) P_(h') v = B(h, h') (v + P_h v),

which is Lemma 15 with u = v and p(h) = P_h v. So either q = 0; or B = 0 and q is linear, and
sigma vanishes on ker q, of codimension 1; or rank B = 2 and q vanishes on rad B, of codimension 2.
In each case sigma vanishes on a subspace of T_y of codimension <= 2, and Lemma 18 gives
n - a + d_y - 2 <= a + 2b, with d_y >= 1. Finally, n <= 2a + 2b + 1 <= 2a + 3b is what
|L| <= |Omega|^4 needs. If Q has full rank, y^T M x runs over all of F_2 as M varies, for every
x != 0, so V_y = 0. QED

**Corollary 12 (a <= 3 and (4, 2)).** If L has a self-centralising normal subgroup
A ~ Z_4^a x Z_2^b with b = 0 or (a - 3)(b - 1) <= 1, then |L| <= |Omega|^4, and the answer is yes.
So the answer is yes whenever a <= 3 (every b), b <= 1, or (a, b) = (4, 2). This contains
Theorems 18 to 20 and settles, for example, (3, 4) and (3, 5).
*Proof.* b = 0 is Theorem 16, so let b >= 1. If a + b <= 2, then a <= 2 and Theorem 17 applies. If
dim S = 0, then e <= 2, and if dim S = 1, Proposition 17 gives n <= a + 2b + 3 <= 2a + 3b. Let
dim S >= 2. If r >= b(a - 2) + 1, use Theorem 21. Otherwise r <= min(b(a - 2), b(a - s)), and
Theorem 17 gives n <= a + s + 2b + r. This is at most a + ab + 2 when s <= 2, and at most
a + 2b + ab - s(b - 1) <= a + ab - b + 3 when s >= 3. Both are <= 2a + 3b when
(a - 3)(b - 1) <= 1. QED

For (a, b) = (5, 2) and (4, 3) the same count leaves exactly one case: s = 2, r = b(a - 2) and
n_0 = a + 2 + 2b (equality in Theorem 17). Then W is all of K_X with X = span sigma(H_0) of
dimension 2, and V_y = X for every y, so Theorem 21 does not apply. The rest of this section (new
in 1.7.4) proves the two-dimensional form of Lemma 15 that this case needs, and with it settles
every a <= 4 and (5, 2).

**Lemma 20 (squares in a plane).** Let X be a 2-dimensional F_2-space, V an F_2-space,
sigma : V -> X a quadratic map with polar form beta, and alpha : V -> End(X) a linear map with

    alpha(h') sigma(h) = (I + alpha(h)) beta(h, h')     for all h, h' in V.

Let K = ker alpha. Then beta(K, K) = 0, sigma is additive on K, and

    rank alpha + dim sigma(K) <= 4,

so sigma vanishes on K_0 = K n ker sigma, a subspace of codimension <= 4.
*Proof.* For h and h' in K the identity reads 0 = beta(h, h'). So sigma is additive on K, sigma(K)
is a subspace, and K_0 has codimension rank alpha + dim sigma(K). For h in K and any h', the
identity gives alpha(h') sigma(h) = beta(h, h'), and with h and h' exchanged it gives
0 = (I + alpha(h')) beta(h', h). Together, A^2 x = A x for every A in alpha(V) and every x in
sigma(K). If sigma(K) = 0, then rank alpha <= dim End(X) = 4. If sigma(K) = span(x) with x != 0,
then alpha(V) is not all of End(X): for y outside span(x), the A with A x = y and A y = 0 has
A^2 x = 0 != A x. So rank alpha <= 3. If sigma(K) = X, every A in alpha(V) is idempotent, and
(A + B)^2 = A + B gives AB = BA, so alpha(V) is a commuting subspace of End(X). A commuting
subspace that contains a non-scalar A lies in span(I, A), so rank alpha <= 2. QED
With dim X = 1 the same argument gives codimension <= 2, which is the last step of Theorem 21
without Lemma 15. Each of the bounds 4, 3 and 2 is the largest dimension of a subspace of End(X)
with the property used (all of End(X); the maps that send x into span(x); the diagonal matrices in
a basis), and `cube_groups/thm22.py` checks this over all 67 subspaces of M_2(F_2).

**Theorem 22 (a slice that meets S in a plane).** In the setting of Theorem 17, suppose that some
y != 0 has dim(V_y n S) = 2. Then n <= 2a + 2b + 4 - d_y <= 2a + 2b + 2. With Theorem 21: if some
y has dim(V_y n S) <= 2, then n <= 2a + 2b + 2, and |L| <= |Omega|^4 when b >= 2. By Lemma 19
this applies whenever r >= b(a - 3) + 1, and it applies whenever dim S <= 2.
*Proof.* Let X = V_y n S and let T_y be as in the proof of Theorem 21, so dim T_y = n - a + d_y and
sigma(T_y) <= X; then beta(T_y, T_y) <= X as well. Choose a complement of X in F_2^a and, for h in
T_y, let alpha(h) in End(X) be P_h restricted to X followed by the projection onto X along that
complement. The P-rows of the identity of Theorem 17, P_(h') sigma(h) = (I + P_h) beta(h, h'), hold
for all h and h' in H. For h and h' in T_y, sigma(h) and beta(h, h') lie in X, and projecting onto X
gives alpha(h') sigma(h) = (I + alpha(h)) beta(h, h'). So Lemma 20 on V = T_y gives a subspace of
T_y of codimension <= 4 on which sigma vanishes, and Lemma 18 gives n - a + d_y - 4 <= a + 2b, with
d_y >= dim X = 2. For the last sentence: if codim W <= 3b - 1, Lemma 19 gives a basis vector y_i
with d_(y_i) <= 2, and then dim(V_(y_i) n S) <= 2. QED

**Corollary 13 (a <= 4 and (5, 2)).** If L has a self-centralising normal subgroup
A ~ Z_4^a x Z_2^b with b = 0 or (a - 4)(b - 1) <= 1, then |L| <= |Omega|^4, and the answer is yes.
So the answer is yes whenever a <= 4 (every b), b <= 1, or (a, b) = (5, 2). This contains
Corollary 12 and settles, for example, (4, 3), (4, 4) and (5, 2).
*Proof.* b <= 1 is Theorems 16 and 17, so let b >= 2. If S = 0, then e <= 2, which is settled. If
dim S <= 2 or r >= b(a - 3) + 1, Theorem 22 gives n <= 2a + 2b + 2 <= 2a + 3b. Otherwise
dim S >= 3 and r <= min(b(a - 3), b(a - s)), and Theorem 17 gives n <= a + s + 2b + r. For s <= 3
this is at most a + 3 + 2b + b(a - 3), and for s >= 3 at most
a + 2b + ab - s(b - 1) <= a + 2b + ab - 3(b - 1). Both equal a + ab - b + 3, which is <= 2a + 3b
exactly when (a - 4)(b - 1) <= 1. QED

For (a, b) = (6, 2) and (5, 3) the same count leaves exactly one case: s = 3, r = b(a - 3) and
n_0 = a + 3 + 2b, so W = K_X with X = span sigma(H_0) of dimension 3 and V_y = X for every y. A
three-dimensional Lemma 20 would settle both if it gave a subspace of T_y of codimension <= b + 3
on which sigma vanishes (Lemma 18 then gives n <= 2a + 3b). The argument above is too weak there:
when sigma(K) = 0 it only bounds the codimension by dim End(X) = 9. (Theorem 24 below gives
codimension <= 3, and Corollary 14 settles both cases.)

The rest of this section (new in 1.7.5) measures exactly how much codimension Lemma 20 needs, and
shows that this one number decides the whole family. Let X be an F_2-space of dimension t and call
a *system* a quadratic map sigma : V -> X with polar form beta, together with a linear map
alpha : V -> End(X), written h -> A_h, satisfying the identity of Lemma 20,

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Let M(t) be the largest, over all systems, of the least codimension of a subspace of V on which
sigma vanishes. By Lemma 21(a) below, M(t) <= t^2 + t, so it is finite.

**Proposition 20 (reduction to M(t)).** In the setting of Theorem 17 with b >= 1, let y != 0 and
t = dim(V_y n S). Then

    n <= 2a + 2b + M(t) - d_y <= 2a + 2b + M(t) - t.

So: (a) if M(t) <= t + 1 for every t <= a, then |L| <= |Omega|^4 for every self-centralising normal
Z_4^a x Z_2^b with b >= 1, and with Theorem 16 the answer is yes for the whole family. (b) If some y
has dim(V_y n S) <= 2, then n <= 2a + 2b; for dim(V_y n S) = 2 this uses the computed value
M(2) = 2 below, so that case is computer-assisted. (c) The open cases (6, 2) and (5, 3) need only
M(3) <= b + 3, that is M(3) <= 5 for (6, 2) and M(3) <= 6 for (5, 3).
*Proof.* Repeat the proof of Theorem 22 with X = V_y n S of any dimension t. The projected maps
alpha(h) make (sigma, alpha) on T_y a system, because the P-rows of the identity of Theorem 17 hold
on all of H and sigma(h), beta(h, h') lie in X for h, h' in T_y. So sigma vanishes on a subspace of
T_y of codimension <= M(t), and Lemma 18 gives n - a + d_y - M(t) <= a + 2b, with d_y >= t because
X <= V_y. For (a), M(t) - t <= 1 <= b gives n <= 2a + 3b. For (b), use M(0) = 0, M(1) = 1
(Lemma 22) and M(2) = 2. For (c), the case left by Corollary 13 has t = d_y = 3. QED

**Lemma 21 (reduced systems).** Let (sigma, alpha) be a system, K = ker alpha and
K_0 = K n ker sigma. (a) K_0 lies in the radical of beta, so sigma and alpha factor through V/K_0,
and the quotient is again a system, of dimension rank alpha + dim sigma(K) <= t^2 + t.
(b) A_h sigma(h) = 0, and A_(h') sigma(h) lies in Im(I + A_h) for all h and h'.
(c) If t >= 2 and alpha(V) = End(X), then sigma = 0.
So M(t) is the largest least codimension over the systems on V = C x F_2^y with alpha the
projection onto a subspace C of End(X) and 0 <= y <= t: a finite list.
*Proof.* (a) For k in K_0, (*) with h = k reads 0 = beta(k, h'). So k is in rad beta, and
sigma(h + k) = sigma(h) + sigma(k) + beta(h, k) = sigma(h); A_(h + k) = A_h. The dimension
count is Lemma 20's: K/K_0 is isomorphic to sigma(K), because sigma is additive on K. Two linear
maps onto C whose kernels have the same dimension differ by an automorphism of V, which carries
solutions to solutions. (b) h' = h in (*) gives the first claim (beta is alternating); (*) itself
gives the second. (c) Suppose sigma(h) = x != 0 and put A = A_h. Since alpha(V) x = X, (b)
makes I + A invertible. So sigma vanishes at every h' whose A_(h') = B has eigenvalue 1. For
such h', (*) with the roles exchanged gives 0 = (I + B) beta(h, h'), and (*) itself gives
B x = (I + A) beta(h, h'). Hence (I + B)(I + A)^(-1) B x = 0 for every B with eigenvalue 1. Since
A x = 0, (I + A)^(-1) x = x. Pick z outside {0, x} and put w = (I + A)^(-1) z; then w is not 0 or x,
so x and w are independent. Let B x = z, and B w = x + w + z if t = 2; if t >= 3, let B w = 0, B u = u
for a third basis vector u, and B = 0 on the rest of a basis. In both cases B has eigenvalue 1
(on x + w, or on u) and (I + B) w != 0 (it is x + z, or w), a contradiction. QED

**Lemma 22 (Lemma 15 needs only codimension 1).** In the setting of Lemma 15, q vanishes on a
subspace of codimension 1. So M(1) = 1, and in Theorem 21 the case V_y n S = span(v) gives
n <= 2a + 2b + 1 - d_y <= 2a + 2b.
*Proof.* If B = 0, q is linear and vanishes on its kernel. If B != 0, the proof of Lemma 15 shows
that q vanishes on R = rad B, that dim V/R = 2, and that q = 1 only on the coset h* + R. Pick c
outside R and outside h* + R. On R + span(c), q(c + r) = q(c) + q(r) + B(c, r) = 0. The system
q = x_1 x_2 + x_2, p = x_1 on F_2^2 satisfies Lemma 15's equation and q != 0, so codimension 1
is needed. QED

**Lemma 23 (a normal form).** Let (sigma, alpha) be a system with dim X = t.
(a) For every h, sigma(h) lies in ker A_h, and ker A_h lies in Im(I + A_h).
(b) If sigma(h) = (I + A_h) lam(h) for a linear map lam : V -> X, then sigma vanishes on ker lam,
a subspace of codimension <= t. For a given linear lam, the map h -> (I + A_h) lam(h) satisfies (*)
if and only if A_h (I + A_h) lam(h') + (A_h A_(h') + A_(h') A_h) lam(h) = 0 for all h and h'.
(c) If rank alpha <= 1 (in particular if t = 1), every system has the form of (b). More generally,
if the form holds on one complement of K = ker alpha, it holds on V, with lam = sigma on K.
(d) M(t) >= t. On V = F_2^(2t) with coordinates (u, v), the maps A_h = diag(u_1, ..., u_t) and
sigma_i(h) = (1 + u_i) v_i form a system; sigma vanishes on {v = 0} and on no subspace of
codimension < t.
*Proof.* (a) Lemma 21(b) gives A_h sigma(h) = 0. Let X_0 be the set of vectors killed by some power
of A_h. A_h is nilpotent on X_0, so I + A_h maps X_0 onto itself, and ker A_h <= X_0 <= Im(I + A_h).
(b) The first claim is clear. Expanding sigma(h + h') gives beta(h, h') = A_h lam(h') + A_(h') lam(h),
and then (I + A_h) beta(h, h') + A_(h') sigma(h) is exactly the displayed expression.
(c) For h and h' in K, (*) reads 0 = beta(h, h'), so sigma is additive on K. Let C' be a complement
of K on which sigma(c) = (I + A_c) lam(c) with lam linear, and put lam = sigma on K. For k in K and
c in C', (*) with h = k and h' = c gives beta(k, c) = A_c sigma(k), so
sigma(c + k) = sigma(c) + sigma(k) + A_c sigma(k) = (I + A_c)(lam(c) + lam(k)), and A_(c + k) = A_c.
If rank alpha = 0, C' = 0. If rank alpha = 1, C' = span(e), and by (a) there is a v with
(I + A_e) v = sigma(e); put lam(e) = v.
(d) beta_i(h, h') = u'_i v_i + u_i v'_i, and (1 + u_i) beta_i(h, h') = u'_i (1 + u_i) v_i, which is
the i-th entry of A_(h') sigma(h), since u_i (1 + u_i) = 0. (This is the form of (b) with lam = v.)
In the coordinates (u_i, v_i), the zero set of sigma_i is {(0, 0), (1, 0), (1, 1)}, which contains
no 2-dimensional subspace. So a subspace U on which sigma vanishes projects to a subspace of
dimension <= 1 in each of the t coordinate planes, dim U <= t, and its codimension is >= t. QED

Version 1.7.5 conjectured at this point that every system has the form of Lemma 23(b). **That is
false**: Example 1 below has no normal form. Lemma 23 and everything before it are unaffected, but
the normal form cannot be the route to M(t) = t. (Theorem 24 below proves M(3) = 3 by another
route; whether M(t) = t for every t is open.) The rest of this section up to Theorem 23 is new in
1.7.6.

**Lemma 24 (when the normal form holds).** Let alpha be one-to-one (by Lemma 23(c) this case is
enough), with basis e_1, ..., e_r of V, A_i = A_(e_i), q_i = sigma(e_i), b_ij = beta(e_i, e_j) and
Fix(A) = ker(I + A).
(a) (*) holds if and only if A_j q_i = (I + A_i) b_ij for all i and j (with b_ii = 0) and
A_k b_ij + A_i b_jk + A_j b_ik = 0 for all distinct i, j and k.
(b) sigma has the form of Lemma 23(b) if and only if there are f_i in Fix(A_i) with

    f_i + f_j + b_ij  in  Fix(A_i + A_j)     for all i < j.

(c) For a *pencil* (r = 2, b = b_12) the form holds if and only if b lies in
Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2). It holds when one of A_1, A_2, A_1 + A_2 is invertible, and
for every pencil when t = 2.
*Proof.* (a) Both sides of (*) are linear in h', so take h' = e_k. Then
Q_k(h) = A_k sigma(h) + (I + A_h) beta(h, e_k) is a quadratic map with Q_k(0) = 0, so it vanishes if
and only if it vanishes at each e_i and its polar form vanishes at each pair e_i, e_j. The first
gives A_k q_i = (I + A_i) b_ik; the polar form of h -> A_h beta(h, e_k) at (e_i, e_j) is
A_i b_jk + A_j b_ik, and that of h -> A_k sigma(h) is A_k b_ij. For k in {i, j} the polar condition
is empty.
(b) By (a), A_i q_i = 0, so (I + A_i) q_i = q_i and the solutions of (I + A_i) lam_i = q_i are
lam_i = q_i + f_i with f_i in Fix(A_i). The quadratic maps sigma and h -> (I + A_h) lam(h) agree at
each e_i; their polar forms at (e_i, e_j) are b_ij and A_i lam_j + A_j lam_i. By (a),
A_j q_i + A_i q_j = (A_i + A_j) b_ij, and with A_i f_i = f_i one checks
A_j f_i + A_i f_j = (I + A_i + A_j)(f_i + f_j). So the polar forms agree if and only if
(I + A_i + A_j)(f_i + f_j) = (I + A_i + A_j) b_ij, which is the displayed condition.
(c) The first sentence is (b) for r = 2. If A_1 is invertible, then q_1 = 0 and (a) gives
(I + A_1) b = A_2 q_1 = 0, so b is in Fix(A_1); A_2 is the same, and for A_1 + A_2 use the basis
e_1, e_1 + e_2, for which beta is still b. For t = 2, suppose no element of the pencil is invertible.
The non-zero singular 2 x 2 matrices have rank 1 and are nilpotent (Fix = 0) or idempotent (Fix =
their image, a line). No pencil in M_2(F_2) is nilpotent throughout (the three non-zero nilpotents
add to invertible matrices), so if the three Fix spaces do not span X, they all lie in one line l and
some element of the pencil is idempotent with image l; change the basis of the pencil so that this
element is A_1. In a basis (u, w) of X with A_1 = E_11, l = span(u), (a) gives q_1 = x w and
A_2 q_1 = (I + A_1) b = b_2 w, where b = b_1 u + b_2 w. If x = 0 or b_2 = 0, b is in l. Otherwise
A_2 w = w, so A_2 = [[a, 0], [c, 1]], and singular means a = 0; then Fix(A_2) = span(w) is not in l,
a contradiction. QED

**Example 1 (no normal form).** Let t = 3 and V = F_2^2, with (1-based matrix entries)

    A_1 = E_11,   A_2 = E_12 + E_13 + E_21 + E_22,   A_1 + A_2 = E_11 + E_12 + E_13 + E_21 + E_22,
    sigma(e_1) = e_2 + e_3,   sigma(e_2) = e_1 + e_2 + e_3,   beta(e_1, e_2) = e_2,

so sigma(e_1 + e_2) = e_1 + e_2. This is a system with no normal form, and sigma vanishes only at 0,
so its least codimension is 2 = dim V.
*Proof.* Lemma 24(a): A_1 q_1 = 0, A_2 q_2 = 0, A_2 q_1 = e_2 = (I + A_1) e_2 and
A_1 q_2 = e_1 = (I + A_2) e_2, so (*) holds. Fix(A_1) = span(e_1), and A_2 and A_1 + A_2 fix no
non-zero vector, so Fix(A_1) + Fix(A_2) + Fix(A_1 + A_2) = span(e_1) does not contain b = e_2, and
Lemma 24(c) applies. Directly: lam(e_1) is e_2 + e_3 or e_1 + e_2 + e_3, lam(e_2) must be
e_1 + e_2 + e_3, and then (I + A_1 + A_2) lam(e_1 + e_2) is 0 or e_2, never
sigma(e_1 + e_2) = e_1 + e_2. QED
The example needs only codimension 2 < t, so it says nothing against M(t) = t. Its solution space
is 1-dimensional and stays so when y = 1, 2 or 3 kernel directions are added.

*Computation (the normal form).* `cube_groups/normal_form.py` (full run on 2026-10-17; every graded
prediction matched) asks for each system whether every solution of (*) has the normal form. All 4
systems with t = 1 and all 201 with t = 2 do. With t = 3, 2,772 of the 175,784 systems with
dim C <= 2 and y <= 3 do not (none with dim C = 1, as Lemma 23(c) says), and 4 of 688 structured
systems do not; with t = 4, 3 of 309 do not. `cube_groups/nf_pencil.py` (full run on 2026-10-17;
every graded prediction matched) checks Example 1 and Lemma 24. Of the 43,435 pencils in M_3(F_2),
693 (756 systems) have no normal form; none of them contains an invertible matrix, and all 756
systems are anisotropic (defined below). Brute force agrees with Lemma 24(c) on 4,581 systems, all
35 pencils in M_2(F_2) have the normal form, and 60 of 3,000 random pencils in M_4(F_2) do not.
Lemma 24(b) agrees with brute force on every 3-dimensional C in M_2(F_2) and on 400 random ones in
M_3(F_2), where the 135 solutions sampled all had the normal form. The solutions outside the normal
form that were sampled all vanish on a subspace of codimension <= t.

*Computation (M(t)).* `cube_groups/plane_search.py` (full run on 2026-10-16; every pre-registered
prediction matched) uses Lemma 21 to list the systems. For t = 1, the 4 systems give M(1) = 1. For
t = 2, all 67 subspaces C of M_2(F_2) with y <= 2 (201 systems, every solution sigma examined and
every least codimension computed exactly by a branch-and-bound search) give M(2) = 2, attained by
20 systems; the three systems with C = End(X) have no non-zero solution (Lemma 21(c)), and K_0 lay
in rad beta every time (Lemma 21(a)). For t = 3 it examined 864 systems built from 18 structured
subspaces of M_3(F_2) (diagonal, triangular, symmetric, the field F_8, Jordan blocks, maps fixing a
line or a plane, and others) and random subspaces of them, 52 of them only on sampled solutions.
The largest least codimension found is 3 (in 23 systems), none needs 4 or more, and C = End(X) again
has no non-zero solution. So M(1) = 1 and M(2) = 2, and Theorem 24 below gives M(3) = 3, as these
samples suggested.

Call a system *anisotropic* if sigma(h) != 0 for every h != 0. Then A_h is singular for every h
outside K (Lemma 21(b)), restrictions to subspaces stay anisotropic, and the least codimension is
dim V. So an anisotropic system with dim V = t + 1 would give M(t) > t.

**Proposition 21 (anisotropic systems; computed).** (a) For t = 1 and t = 2 the largest anisotropic
systems have dim V = t. (b) For t = 3 there are anisotropic systems with dim V = 3 (for example 14
of the 52,157 systems whose C is a 3-dimensional subspace of singular matrices and y = 0 have one;
Example 1 is one with dim V = 2), but none with dim V = 4. (c) So for t = 3 every system with
dim V >= 4 has a non-zero zero of sigma, and its least codimension is at most dim V - 1.
*Computation.* `cube_groups/nf_pencil.py` lists every subspace C of M_t(F_2) whose non-zero
elements are all singular (for t = 3 there are 343, 13,279, 52,157 and 22,050 of dimensions 1 to
4) and, for every y = dim V - dim C <= t, examines every solution of (*). For t = 3 and dim V = 4
that is 87,829 systems, and no solution is anisotropic. Every system with dim V = 4 is one of these
up to a change of basis of V, or has an invertible A_h with h != 0 and then sigma(h) = 0 by
Lemma 21(b), or has alpha = 0, in which case sigma is linear on F_2^4. For (c), restrict to any
4-dimensional subspace. QED (computer-assisted)

Write LC(V) for the least codimension of a subspace of V on which sigma vanishes, and call a
matrix A *good* if A and I + A are both invertible.

**Lemma 25 (zeros of sigma).** Let (sigma, alpha) be a system.
(a) If sigma(u) = 0, then beta(u, h) lies in Fix(A_u) for every h. So u^perp = {h : beta(u, h) = 0}
has codimension at most dim Fix(A_u), and if u != 0 and W is a complement of span(u) in u^perp,
then LC(V) <= codim(u^perp) + LC(W), where W carries the restricted system.
(b) If A_u is invertible, then sigma(u) = 0. If A_u is good, then u also lies in the radical of
beta. The span R of all u with A_u good lies in the radical of beta, sigma vanishes on R, and
sigma(h + r) = sigma(h) for every r in R.
(c) Let S be the span of the good elements of alpha(V), E a complement of S in alpha(V) and
W = alpha^(-1)(E). Then E contains no good element, dim W = dim V - dim S, and LC(V) <= LC(W).
*Proof.* (a) Put h = u in (*): 0 = A_(h') sigma(u) = (I + A_u) beta(u, h'). Since beta is
alternating, u lies in u^perp. If sigma vanishes on a subspace U of W, then for w in U,
sigma(w + u) = sigma(w) + sigma(u) + beta(w, u) = 0, so sigma vanishes on U + span(u), whose
codimension in V is codim(u^perp) + (dim W - dim U).
(b) A_u sigma(u) = 0 by Lemma 21(b). If A_u is good, Fix(A_u) = 0 and (a) gives beta(u, .) = 0. So
R lies in the radical, and sigma(u + r) = sigma(u) + sigma(r) + beta(u, r) shows by induction that
sigma vanishes on R. Then sigma(h + r) = sigma(h) + sigma(r) + beta(h, r) = sigma(h).
(c) A good element of E would lie in S n E = 0. Choose u_1, ..., u_s in V such that the A_(u_i)
are good and form a basis of S, and put R' = span(u_i). Then V = W + R', and W n R' = 0 because
alpha is one-to-one on R' and alpha(R') n E = 0. If sigma vanishes on U <= W, it vanishes on
U + R' by (b), and U + R' has the same codimension in V as U has in W. QED

For t = 3 the good matrices are exactly the 48 elements of order 7 of GL_3(F_2): a good A has no
eigenvalue in F_2, so its characteristic polynomial is x^3 + x + 1 or x^3 + x^2 + 1. Each of them
generates a copy F_2[A] of the field F_8 inside M_3(F_2), whose non-zero elements are I and six
elements of order 7, so there are 8 such copies.

**Theorem 23 (t = 3).** Let t = 3.
(a) Every system with dim V >= 4 has LC(V) <= dim V - 1 (Proposition 21).
(b) Every system with dim V <= 7 has LC(V) <= 5.
(c) Every hyperplane of M_3(F_2) contains at least 16 elements of order 7, so a subspace with no
element of order 7 has dimension at most 7; the stabilisers of a line and of a plane are such
subspaces of dimension 7. By Lemma 25(c), M(3) is the largest LC over the reduced systems of
Lemma 21 whose C has no element of order 7; these have dim C <= 7 and dim V = dim C + y <= 10.
(d) M(3) <= 7, and LC(V) <= 6 whenever dim V <= 8. More generally, if s is the dimension of the
span of the elements of order 7 in alpha(V), then LC(V) <= 5 whenever dim(V/K_0) - s <= 7, and
LC(V) <= 6 whenever dim(V/K_0) - s <= 8.
So M(3) <= 5, which would settle (6, 2) and (5, 3) by Proposition 20(c), now needs only the reduced
systems whose C has no element of order 7, with 5 <= dim C <= 7 and dim C + y >= 8. M(3) <= 6, which
would settle (5, 3), needs only those with dim C + y >= 9.
*Proof.* (b) If dim V <= 5 there is nothing to prove, and dim V = 6 is (a). Let dim V = 7. If I is
not in alpha(V), let u be any non-zero zero of sigma. Otherwise choose a hyperplane H of alpha(V)
that does not contain I, and a non-zero zero u of sigma in alpha^(-1)(H), which has dimension
6 >= 4. Either way A_u != I, so dim Fix(A_u) <= 2, and Lemma 25(a) gives LC(V) <= c + LC(W) with
c = codim(u^perp) <= 2 and dim W = 6 - c. By (a), LC(W) <= 5, 4 and 3 for c = 0, 1 and 2.
(c) Let F be one of the 8 copies of F_8, and let f(X) = tr(M X) be a non-zero linear form. The
kernel of f on F has dimension >= 2, so it contains at least three non-zero elements of F, and at
least two of them have order 7. The copies share no element of order 7, so the hyperplane ker f
contains at least 16 of them. An element of order 7 has an irreducible characteristic polynomial,
so it fixes no line and no plane. The rest is Lemma 25(c) applied to a reduced system: there
dim V = dim C + dim sigma(K) by Lemma 21(a), and dim sigma(K) <= 3.
(d) Let L(m) be the largest LC over the systems with dim V = m. For m >= 5 the argument of (b) gives
a non-zero zero u with A_u != I, so L(m) <= max(L(m - 1), 1 + L(m - 2), 2 + L(m - 3)). With
L(4) <= 3, L(5) <= 4, L(6) <= 5 and L(7) <= 5 this gives L(8) <= 6, L(9) <= 7 and L(10) <= 7, and
by (c) only dim V <= 10 matters. For the last sentence, pass to the reduced system V/K_0
(Lemma 21(a)) and apply (b), or L(8) <= 6, to W in Lemma 25(c), which has dimension
dim(V/K_0) - s. QED (computer-assisted through Proposition 21)

*Computation.* `cube_groups/m3_core.py` (new in 1.7.6; full run on 2026-10-17, every graded
prediction matched) checks Lemma 25 and Theorem 23(a) and (b) on random systems, and the facts
about elements of order 7 used in (c): there are 48, they span M_3(F_2), every hyperplane contains
at least 16 of them (some exactly 16), no 8-dimensional subspace avoids them, and the 14
stabilisers do. It lists, up to conjugacy, every subspace of M_3(F_2) of dimension 5, 6 and 7 with
no element of order 7 (167,629, 5,279 and 22 of them, in 1,192, 68 and 3 classes) and examines
every solution of (*) on the systems they give: none needs codimension above 5, and in the 940
cases where it computed the least codimension exactly, it was 1 or 2. Theorem 24 below makes this
search unnecessary for M(3); it is now a consistency check, and it agrees.

From here to the computation after Corollary 14, this section is new in 1.7.7. It replaces the
search of Theorem 23 by one lemma.

**Lemma 26 (restriction at a vector).** Let (sigma, alpha) be a system, u in V, rho = rank A_u,
X_1 = ker A_u and U = {h in V : beta(h, u) = 0}.
(a) sigma(U) lies in X_1. Fix a complement of X_1 in X and, for h in U, let alpha_1(h) in End(X_1)
be A_h restricted to X_1 followed by the projection onto X_1. Then sigma on U, with alpha_1, is a
system with dim X_1 = t - rho. The same projection makes any subspace U' a system with values in
any subspace X' that contains sigma(U').
(b) codim U <= t. If sigma(u) = 0, then codim U <= dim Fix(A_u) <= rho.
(c) So if sigma(u) = 0, then LC(V) <= dim Fix(A_u) + M(t - rho) <= rho + M(t - rho). If A_u is
invertible, sigma vanishes on U, so LC(V) <= t.
*Proof.* (a) Put h' = u in (*): A_u sigma(h) = (I + A_h) beta(h, u), which is 0 for h in U. For U'
and X' as in the last sentence, beta(h, h') = sigma(h + h') + sigma(h) + sigma(h') lies in X' for
h, h' in U'. Let alpha'(h) be A_h restricted to X' followed by the projection onto X' along a
fixed complement. Apply this projection to (*): the left side becomes alpha'(h') sigma(h), and,
since beta(h, h') is in X', the right side becomes (I + alpha'(h)) beta(h, h'). The first claim is
the case U' = U, X' = X_1. (b) U is the
kernel of the linear map h -> beta(h, u) into X. If sigma(u) = 0, Lemma 25(a) puts its image into
Fix(A_u), and Fix(A_u) n ker A_u = 0 gives dim Fix(A_u) <= t - dim ker A_u = rho. (c) A subspace of
U on which sigma vanishes has codimension in V at most codim U plus its codimension in U. If A_u is
invertible, X_1 = 0. QED

Let A(t) be the largest dim V of an anisotropic system with dim X = t. An anisotropic sigma is a
t-tuple of quadratic forms with only the trivial common zero, so A(t) <= 2t by Chevalley-Warning,
and a linear one-to-one sigma with alpha = 0 shows A(t) >= t.

**Theorem 24 (M(t) is decided by anisotropic systems).** For every t >= 1,

    max(t, A(t)) <= M(t) <= t + max over 1 <= s <= t of max(A(s) - s, 0).

So M(t) <= 2t; M(t) = t for every t if and only if A(t) <= t for every t; and M(t) <= t + 1 for
every t <= a if A(s) <= s + 1 for every s <= a. With A(1) = 1, A(2) = 2 and A(3) = 3 (Lemma 22 and
Proposition 21), M(1) = 1, M(2) = 2 and **M(3) = 3**.
*Proof.* The lower bound is Lemma 23(d) and the fact that an anisotropic system has LC = dim V.
For the upper bound write E(t) for the maximum on the right and induct on t, with M(0) = 0. Given
a system, pass to the reduced system on V/K_0 (Lemma 21(a)), which has the same least codimension.
If it is anisotropic, LC = dim V <= A(t) <= t + E(t). Otherwise sigma has a zero u != 0, and
A_u != 0, because a zero in K = ker alpha would lie in K_0. With rho = rank A_u >= 1, Lemma 26(c)
and the induction hypothesis give LC <= rho + (t - rho) + E(t - rho) <= t + E(t). M(t) <= 2t
follows from A(s) <= 2s. A(1) <= M(1) = 1 is Lemma 22. QED (for t = 2 and 3, computer-assisted
through Proposition 21.)

So every system with t = 3 has a vanishing subspace of codimension <= 3, which is sharp by
Lemma 23(d), and Theorem 23 is superseded. It stays true, and `m3_core.py` still checks it.

**Remark (what the search of Theorem 23 would have met).** Two facts found on the way, both proved
by hand, show why the systems left by Theorem 23 are few. (a) For k in K = ker alpha, x = sigma(k)
satisfies A(A + I) x = 0 for every A in alpha(V), by the argument of Lemma 20. For t = 3, if these x
fill a plane Y, then dim alpha(V) <= 5. (In a basis with Y = span(e_1, e_2), write A as blocks
P (Y -> Y), v^T (Y -> span(e_3)), u and w. The condition reads P^2 + P + u v^T = 0 and
v^T (P + (w + 1) I) = 0. The A with v = 0 form a subspace C_0 whose P lie in a commuting space P_0
of idempotents, of dimension <= 2, so dim C_0 <= 5. Polarising the second equation, every A in C_0
gives v_B^T (P_A + w_A I) = 0 for every B. Let r be the dimension of the span of the v_B, so
dim C_0 = dim alpha(V) - r, and suppose dim alpha(V) >= 6. Then r >= 1. If r = 2, then P_A = w_A I
for every A in C_0, a space of dimension <= 3 < 4. If r = 1, then dim C_0 = 5, so C_0 is all of
{P in P_0, any u, any w}, which contains E_33, and then v_B = 0 for every B, a contradiction.) If
the x fill X, alpha(V) is a commuting space of idempotents, of dimension <= 3.
(b) Every 7-dimensional subspace of M_3(F_2) with no element of order 7 contains I: it meets each
copy F of F_8 in a subspace of dimension >= 1, and the only non-zero element of F that does not
have order 7 is I. Besides the 14 stabilisers there are at least 8 more. Identify X with F
and let C_F = {z -> e z + a z^2 + b z^4 : e in F_2, a, b in F}, a 7-dimensional space. If a b != 0,
the map z -> a z^2 + b z^4 kills the square root of a/b. If b = 0 != a, then z + a z^2 kills 1/a.
If a = 0 != b, then z + b z^4 kills the cube root of 1/b, which exists because 3 is prime to 7. So
no A in C_F has A and I + A both invertible. The full run of `m3_core.py` found exactly 22 such
subspaces, in 3 conjugacy classes of sizes 7, 7 and 8, so the 14 stabilisers and the 8 spaces C_F
are all of them (this count is computed, not proved by hand).

**Proposition 22 (anisotropic systems).** Let (sigma, alpha) be anisotropic with dim X = t. Then
every A_h is singular, and:
(a) if some A_u has rank rho, then dim V <= t + A(t - rho);
(b) if every A_h has rank <= 1, then either all A_h have one common image line, and dim V <= t, or
all have one common kernel, and dim V <= 2 + A(t - 1);
(c) hence A(t) <= max(t, 2 + A(t - 1), t + A(t - 2)) for t >= 2, so A(4) <= 6 and A(5) <= 8.
Also A(t_1 + t_2) >= A(t_1) + A(t_2), and A is non-decreasing.
By Theorem 24, M(4) <= 4 + 2 = 6 and M(5) <= 5 + 3 = 8.
*Proof.* A_h sigma(h) = 0 with sigma(h) != 0 makes A_h singular. (a) By Lemma 26(a), U carries an
anisotropic system with dim X_1 = t - rho, and codim U <= t. (b) In a linear space of matrices of
rank <= 1, any two non-zero elements x f and y g share the image (x = y) or the kernel (f = g), since
otherwise x f + y g has rank 2; and if x f and x g with f != g are present, a third element y f'
with y != x would need f' = f and f' = g. So one image or one kernel is common to all. Common image
span(x_0): A_h = x_0 f_h with f_h linear in h, and (*) reads
beta(h, h') = x_0 (f_(h')(sigma(h)) + f_h(beta(h, h'))), so beta takes values in span(x_0). Then
sigma modulo x_0 is additive, so linear, and on its kernel U' (codimension <= t - 1) sigma takes
values in span(x_0). By Lemma 26(a), U' is an anisotropic system with t = 1, so dim U' <= A(1) = 1.
Common kernel ker f_0: A_h = g_h f_0 with g_h linear in h. Apply f_0 to (*): with q = f_0(sigma),
B = f_0(beta) and p(h) = f_0(g_h), q(h) p(h') = B(h, h') (1 + p(h)), which is Lemma 15 with a = 1.
So q vanishes on a subspace R of codimension <= 2 (rad B if B != 0; ker q if B = 0; all of V if
q = 0), and on R sigma takes values in ker f_0. By Lemma 26(a), R is an anisotropic system with
t - 1, so dim R <= A(t - 1). (c) If alpha = 0, sigma is linear and one-to-one, so dim V <= t. If
some A_h has rank >= 2, use (a) with A(t - rho) <= A(t - 2). Otherwise use (b). For the sum, put
two systems side by side (block-diagonal A_h, sigma = (sigma_1, sigma_2)); adding a coordinate on
which sigma is 0 shows that A is non-decreasing. QED

**Corollary 14 (a <= 7, and a <= b + 2).** If L has a self-centralising normal subgroup
A ~ Z_4^a x Z_2^b with b <= 1 or a <= max(7, b + 2), then |L| <= |Omega|^4, and the answer is yes.
This contains Corollary 13 and settles, for example, (6, 2), (5, 3), (7, 2), (6, 3), (7, 5) and
(10, 8). The first open cases are (8, b) for 2 <= b <= 5 and (b + 3, b) for b >= 6.
*Proof.* b <= 1 is Theorems 16 and 17, so let b >= 2; if S = 0, then e <= 2. By Theorem 24,
M(t) - t <= E(t), where E(1) = E(2) = E(3) = 0, E(4) <= 2 and E(5) <= 3 by Proposition 22, and
E(t) <= t always. Let tau be the largest t <= a with E(s) <= b for every s <= t. So tau >= min(a, 4)
when b = 2, tau >= min(a, 5) when 3 <= b <= 5, and tau >= min(a, b) when b >= 6. If some y != 0 has
dim(V_y n S) = t <= tau, Proposition 20 gives n <= 2a + 2b + M(t) - t <= 2a + 3b. This happens when
dim S <= tau, and, by Lemma 19, when codim W <= (tau + 1) b - 1, that is r >= b(a - tau - 1) + 1.
Otherwise dim S >= tau + 1 and r <= min(b(a - tau - 1), b(a - s)), and Theorem 17 gives
n <= a + s + 2b + r <= a + 2b + ab - (tau + 1)(b - 1) (use the first bound on r when
s <= tau + 1 and the second when s >= tau + 1). This is <= 2a + 3b exactly when
(a - tau - 2)(b - 1) <= 1: for b = 2 when a <= tau + 3, and for b >= 3 when a <= tau + 2. With the
values of tau above this is a <= 7 for 2 <= b <= 5 and a <= b + 2 for b >= 6. QED (computer-assisted
through Proposition 21, via Theorem 24 and Proposition 22.)

For the first open case (8, 2), the same count needs tau >= 5, that is E(5) <= 2, which holds if
A(5) <= 7. For (8, b) with 3 <= b <= 5 it needs tau >= 6, which holds if A(6) <= 6 + b. Both would
follow from A(t) = t, which is true for t <= 3.

*Computation (new in 1.7.7).* `cube_groups/m3_exact.py` checks Lemma 26 at every vector of
random solutions with t = 2 and 3, on Example 1 and on the system of Lemma 23(d), and Theorem 24
(every least codimension <= t) on those solutions; Lemma 26(c) for invertible A_u; Proposition 22(b)
on the common-image and common-kernel spaces with t = 2 and 3; and the case count of Corollary 14
for every a <= 14 and b <= 12. These unit tests passed before 1.7.7 was published. The full run
(on 2026-10-17; every graded prediction matched) checked Lemma 26 at 1,408 vectors of 279 random
solutions on 360 systems with t = 2, 3 and 4 (1,097 of them zeros of sigma) with no violation, and
the largest least codimensions it found were 2, 3 and 4 for t = 2, 3 and 4. It checked
Proposition 22(b) on 804 systems over every subspace of the common-image and common-kernel spaces
with t <= 4 (6,241 solutions) with no violation; the anisotropic systems there had dim V <= t. A
random search over 1,140 systems with t = 4 and dim V = 5, 6 and 7 (858,020 solutions) found no
anisotropic system. Most of the spaces it used are reducible in the sense of Lemma 27 below, where
dim V <= 4 is now proved, so this search says little about A(4). The case count of Corollary 14
matched for every a <= 14 and b <= 12.

The rest of this section is new in 1.7.8. It shows that only irreducible spaces of matrices can
stand between the results above and A(t) = t. Call a subspace Y of X *invariant* if A_h Y <= Y for
every h, and call alpha(V) *irreducible* if 0 and X are its only invariant subspaces.

**Lemma 27 (invariant subspaces).** Let (sigma, alpha) be a system and Y an invariant subspace of
dimension d, with 0 < d < t. Then:
(a) sigma modulo Y, with the maps that the A_h induce on X/Y, is a system with t - d;
(b) on every subspace U of V on which sigma modulo Y vanishes, sigma with the restrictions of the
A_h to Y is a system with d;
(c) LC(V) <= M(t - d) + M(d), and an anisotropic system has dim V <= M(t - d) + A(d).
*Proof.* (a) Since Y is invariant, A_h and I + A_h induce maps on X/Y, and (*) holds modulo Y.
(b) For h and h' in U, sigma(h) and beta(h, h') = sigma(h + h') + sigma(h) + sigma(h') lie in Y,
so (*) for h, h' in U is an identity between vectors of Y, in which only the restrictions of A_h
and A_(h') to Y occur. (c) By (a) there is such a U of codimension <= M(t - d), and by (b) a
subspace of U, of codimension <= M(d) in U, on which sigma vanishes. If the system is anisotropic,
so is its restriction to U, and dim U <= A(d). QED

A linear space of matrices of rank <= 1 has a common image line or a common kernel hyperplane
(proof of Proposition 22(b)), and both are invariant. So for t >= 2 an irreducible alpha(V) contains
a matrix of rank >= 2 (and alpha(V) = 0 is not irreducible). In the common-kernel case, Lemma 27
with Y = ker f_0 sharpens Proposition 22(b) to dim V <= M(1) + A(t - 1) = 1 + A(t - 1).

**Lemma 28 (a hyperplane mapped into a line).** Let X = P + span(q) with P a hyperplane and q not
in P, and suppose that every A_h maps P into span(q). Then sigma vanishes on a subspace of
codimension <= t, and an anisotropic system has dim V <= t.
*Proof.* Write sigma(h) = sigma_P(h) + tau(h) q with sigma_P(h) in P, so that tau is a quadratic
form, with polar form b, and write A_h q = pi(h) + mu(h) q with pi : V -> P linear. If pi = 0, every
A_h has image in span(q), and the common-image part of the proof of Proposition 22(b) applies:
beta takes values in span(q), sigma modulo q is linear and vanishes on a subspace U' of
codimension <= t - 1, and on U' sigma is a system with t = 1 (Lemma 26(a)), so it vanishes on a
subspace of U' of codimension <= M(1) = 1; an anisotropic system has dim U' <= A(1) = 1. Now let
pi != 0. Since A_(h') sigma_P(h) lies in span(q), the P-part of (*) reads

    tau(h) pi(h') = beta_P(h, h') + b(h, h') pi(h),

where beta_P is the P-part of beta. With h' = h this gives tau(h) pi(h) = 0. Exchanging h and h'
and adding (beta_P is symmetric) gives (tau(h) + b(h, h')) pi(h') = (tau(h') + b(h, h')) pi(h).
Fix h_0 with pi(h_0) != 0; for k in ker pi this gives tau(k) = b(k, h_0). So tau vanishes on
W = {h : b(h, h_0) = 0}, a subspace of codimension <= 1: on W n ker pi because tau = b(., h_0)
there, and on W outside ker pi because tau(h) pi(h) = 0. Hence sigma(W) lies in P. By the last
sentence of Lemma 26(a), with X' = P and the complement span(q), sigma on W is a system whose maps
are A_h restricted to P and projected onto P along span(q), that is 0. So (*) on W reads
beta(h, h') = 0: sigma is linear on W and vanishes on its kernel, of codimension <= t - 1 in W. If
the system is anisotropic, sigma is one-to-one on W, so dim W <= t - 1 and dim V <= t. QED
If q lies in P instead, span(q) is invariant and Lemma 27 applies. The matrices of Lemma 28 have
rank <= 2, and for t >= 2 the whole space {A : A P <= span(q)}, of dimension 2t - 1, is
irreducible: an invariant subspace containing some p != 0 in P contains A p = q for a suitable A,
and then all of X, since A q can be any vector; and a line span(p + q) with p in P is moved off
itself by an A with A p = 0 and A q outside it.

**Corollary 15 (where an anisotropic system with dim V > t must live).** Let t >= 2 and suppose that
A(s) = s for every s < t, so that M(s) = s for every s < t (Theorem 24). If an anisotropic system
has dim V > t, then alpha(V) is irreducible, its elements are all singular, it contains a matrix
of some rank rho >= 2, and then dim V <= 2t - rho; and there is no hyperplane P and vector q
outside P with A_h P <= span(q) for every h. In particular:
(a) A(4) >= 5 would need such a space in M_4(F_2), and A(4) = 6 would need one whose elements all
have rank <= 2;
(b) whatever A(4) is, an anisotropic system with t = 5 and dim V >= 8 would need an irreducible
space of matrices of rank <= 2 in M_5(F_2), not of the form of Lemma 28. If there is none, then
A(5) <= 7, and the count after Corollary 14 settles (8, 2).
*Proof.* If alpha(V) is reducible, Lemma 27 gives dim V <= M(t - d) + A(d) = t. Lemma 28 gives
dim V <= t, and alpha(V) = 0 gives a linear one-to-one sigma. The elements are singular by
Proposition 22, and an element of rank rho gives dim V <= t + A(t - rho) = 2t - rho by
Proposition 22(a). (a) With A(1), A(2), A(3) = 1, 2, 3, an element of rank 3 gives dim V <= 5.
(b) Let t = 5. If alpha(V) is reducible, Lemma 27 gives dim V <= max(M(4) + A(1), M(3) + A(2),
M(2) + A(3), M(1) + A(4)) <= 7, using M(4) <= 6 and A(4) <= 6 (Proposition 22). An element of rank
rho >= 3 gives dim V <= 5 + A(5 - rho) <= 7. Lemma 28 excludes its form. QED (computer-assisted
through Proposition 21, which gives A(2) and A(3).)

Spaces of matrices of rank at most 2 have been classified. According to the abstract of
C. de Seguins Pazzis, "Primitive spaces of matrices with upper rank two over the field with two
elements" (arXiv 1405.1575), the classification was known over every field with more than two
elements, and that paper completes it over F_2. We have not read it, so nothing here depends on
it. Checking the irreducible spaces of rank at most 2 in M_4(F_2) and M_5(F_2) against Lemma 28 is
the natural next step, for A(4) and for (8, 2).

*Computation (queued).* `cube_groups/m4_irred.py` (new in 1.7.8) checks Lemma 27 on random systems
with t = 3 and 4 whose alpha(V) keeps a coordinate subspace invariant (the quotient and restricted
systems, LC(V) <= codim U + LC(U), and LC(V) <= t), and Lemma 28 on random systems with t = 3 and 4
that map a coordinate hyperplane into a line (tau pi = 0, the subspace W, beta = 0 on W, and
LC(V) <= t). It also searches for anisotropic systems with t = 4 and dim V = 5 and 6 over random
irreducible spaces of singular matrices: subspaces of the spaces {A : A P <= Q} with
(codim P, dim Q) = (1, 1), (1, 2) and (2, 1), and random ones, with reducible spaces as a control.
A second control counts how many random quadratic maps F_2^5 -> F_2^4 are anisotropic (about one
in seven is expected), which shows that the identity (*) is what rules them out. Its unit tests
passed before this version was published, and its full run is queued with pre-registered
predictions.

*Status of Theorems 16 to 24, Lemmas 21 to 28 and Corollary 15.* They are proved by hand above.
Full runs in a sealed container passed on 2026-10-15, 2026-10-16 and 2026-10-17, and every graded
number matched its prediction:
`cube_groups/z4degree.py` (Theorem 16: 6 of 6 groups consistent, both controls as predicted);
`cube_groups/z4z2.py` (Theorem 17: 10 of 10 groups consistent, 4 of them with rank Q > 0, and the
control with a non-central involution fails as predicted); `cube_groups/hommap.py` (the lemma in
Theorem 18: the predicted nullity for every a <= 5 and b <= 4, and brute force agrees on 8 small
pairs); `cube_groups/case42.py` (Lemma 15 for n <= 5, Lemma 16, Proposition 18 for 7 pairs up to
(5, 2), (3, 3) and (2, 4) with its polar-only control, the counting step of Proposition 17, and the
table of N(W) and Lam(W) in codimension 2); `cube_groups/case33.py` (Proposition 19 over every W of
codimension <= b - 1 for nine pairs up to (3, 3) and (2, 4), both controls, the linear core of
Lemma 17, and the case count of Theorem 20); `cube_groups/thm21.py` (Lemma 19 over every W of
codimension <= 2b for nine pairs (a, b) up to (4, 2), (2, 3) and (2, 4), with no violation and the
predicted sharpness counts at codimension 2b; the case count of Corollary 12 for every a <= 8 and
b <= 8; and, on the explicit groups of z4z2.py and its control, that sigma(T_y) lies in V_y and
that Lemma 18 holds, which is only a consistency check because those groups are small);
`cube_groups/thm22.py` (Lemma 20 on 904 systems, every subspace C of M_2(F_2) with m = 2 to 8,
with no violation of any of its claims, rank alpha + dim sigma(K) <= 4 and codim K_0 <= 4 every
time; the table of largest subspaces in its proof; the control, where 87 of 200 random sigma on
F_2^7 vanish on no subspace of codimension <= 4, so the identity is needed; and the case count of
Corollary 13 for every a <= 8 and b <= 8, which leaves (6, 2) and (5, 3) open with s = 3 and r = 6
only); `cube_groups/plane_search.py` (Lemmas 21(a) and 21(c), Lemma 22, and the values of M(t)
above); `cube_groups/normal_form.py` (Lemma 23(a) pointwise, Lemma 23(c) on every system with
dim C = 1, Lemma 23(d) for t = 1, 2, 3, and the normal-form counts above);
`cube_groups/nf_pencil.py` (Example 1, Lemma 24(a) and (c) against the identity and brute force,
Lemma 24(b) on 3-dimensional C, and Proposition 21); `cube_groups/m3_core.py` (Lemma 25,
Theorem 23 and the search after it); and `cube_groups/m3_exact.py` (Lemma 26, Theorem 24,
Proposition 22(b) and the case count of Corollary 14). The full run of `cube_groups/m4_irred.py`
(Lemmas 27 and 28) is queued; its unit tests passed. The group-theoretic steps of Proposition 17,
Lemma 18, Theorems 19 to 22, Corollaries 12 to 14 and Proposition 20 are checked by hand only.

**Where the question stands.** Proved: e <= 2; class 2 (Theorem 15); e = 3 with x -> x^4 a
homomorphism; groups with a unique-involution series of length k; a self-centralising normal
Z_4^k; a self-centralising normal Z_4^a x Z_2^b when b <= 1, when a <= 7 (every b) and when
a <= b + 2 (Corollary 14), and also when rank Q >= b(a - 2) + 1 (in particular when Q has full
rank), when ab - s(b - 1) <= a + b, and when dim span sigma(H) <= 1 and a + b >= 3. Reduced: by
Proposition 20 and Theorem 24, every remaining Z_4^a x Z_2^b case follows from A(t) <= t + 1 for
every t, a statement about anisotropic quadratic maps over F_2 alone; the first open case (8, 2)
needs only A(5) <= 7, and by Corollary 15 only an irreducible space of matrices of rank <= 2 in
M_5(F_2), not of the form of Lemma 28, could stand in its way. Known: M(1) = 1, M(2) = 2, M(3) = 3
and M(t) <= 2t for every t; A(t) = t for t <= 3, 4 <= A(4) <= 6, A(5) <= 8 and t <= A(t) <= 2t; at
the least t where A(t) = t fails (if there is one), every counterexample has an irreducible
alpha(V) (Corollary 15). Whether A(t) = t (equivalently, M(t) = t) for every t is open. Computed:
true on every subgroup of Q_16, Q_32, Q_8^2 and Q_16 x Q_8, and of nine class-2 groups up to order
256. An exact search over all 324 conjugacy classes of 7-dimensional subspaces of M_3(F_2) found no
counterexample with A ~ Z_4^3, as Theorem 16 predicts. Open: Z_4^a x Z_2^b with a >= max(8, b + 3),
starting with (8, 2), (8, 3), (8, 4) and (8, 5); homocyclic Z_(2^m)^k with m >= 3; the general
case. A classification of the 2-groups with exactly three involutions (k = 2) is in Janko,
J. Algebra 291 (2005) 505-533. We could not read it, so the case k = 2 is not claimed.

*Prior work.* Searches on 2026-10-15 and 2026-10-16 found no statement of this question. The
literature's "2-central" means Omega_2 <= Z, which is a stronger hypothesis. Higman's Suzuki
2-groups (1963) are the case e = 2 in a special setting. In section 2 of arXiv math/0009003, Bovdi
and Dokuchaev consider a non-abelian 2-group G of exponent 4 whose involutions are central, with
Phi(G) = Omega(G) of order 4, and cite a result of N. Blackburn (Huppert and Blackburn, Finite
Groups II, Theorem VIII.5.4) for |G| <= |Omega(G)|^3. That is our bound for e = 2 in their setting,
so the case e = 2 may well be known more generally; we have not read Blackburn's theorem. A search
on 2026-10-17 found Pakianathan and Yalcin, "Quadratic maps and Bockstein closed group extensions"
(arXiv math/0606374), on central extensions of elementary abelian 2-groups through their quadratic
maps, including the map A -> A + A^2 on gl_n(F_2). From its abstract and a search summary of its
text (we have not read it in full), it appears to record the Chevalley-Warning bound for quadratic
maps with no non-trivial zero, with equality for Q_8^m, which is the argument of Lemma 10. We found
nothing on the identity (*) or on M(t). The tools (quadratic maps, Chevalley-Warning, determinants
of degree-bounded matrices, spaces of rank-1 matrices, invariant subspaces) are standard, so a
specialist may know these bounds. Please open an issue if so.

## Verification table

Every module below is in `cube_groups/` (pure Python, no dependencies). `python -m unittest -v` at
the top of the repository runs all their unit tests, and running a module as a script
(`python cube_groups/<module>.py --help`) runs its full check. The full runs were done in a sealed container on
2026-10-15, 2026-10-16 and 2026-10-17. The module docstrings use the labels of our working drafts; the
concordance below maps them to this file.

| module | statements | full run |
|---|---|---|
| robust_cubes.py | Theorem 9, Corollary 9 (16 abelian groups, r = 1..4; entropy laws) | passed |
| frobenius_cubes.py | Proposition 5 (thresholds 257, 67, 59, 73, 107) | passed |
| heisenberg_cubes.py | Proposition 6 (least-k table; S_3^9) | passed |
| hamiltonian_cubes.py | Lemma 9 (Q_8 case), Proposition 13 (Q_8^15, Q_8^12) | passed |
| pcentral_cubes.py | Lemma 9, P(p), Proposition 15 | passed |
| central_density.py | Proposition 12, Corollary 11, Theorem 14, the section 14 question on 4 groups | passed |
| theorem19.py | Theorem 15 (9 class-2 groups; Q_16 control) | passed |
| z4search.py | Lemma 13 at k = 3 (324 orbits, none survives) | passed |
| cubeloss.py | Theorem 11 set form (every K, 6 groups), l_r, G(p, k) ratios | passed |
| orderlp.py | Theorem 12 LP, lam_2 to lam_7 with exact rationals | passed |
| prop31_cubes.py, twosided.py | Proposition 11, Lemma 7, b values, Stab_R(K) = H with core 1 | passed |
| theorem29.py | Theorem 13, Theorem 12 set form, Propositions 7, 8 and 10 (LP) | passed |
| fibre.py | Theorem 10, Proposition 9, b(Gamma) by brute force | passed |
| z4degree.py | Theorem 16 (Q_8, Q_8^2, Q_8^3, P_32, Q_8 x P_32, P_32^2; two controls) | passed |
| z4z2.py | Theorem 17 (10 groups; control), the identity behind Lemma 17 | passed |
| hommap.py | the lemma in Theorem 18 | passed |
| case42.py | Lemmas 15 and 16, Proposition 18, the counting step of Proposition 17 | passed |
| case33.py | Proposition 19 (two controls), the linear core of Lemma 17, the case count of Theorem 20 | passed |
| thm21.py | Lemma 19 (with its sharpness count), the case count of Corollary 12, a group check of Lemma 18 and Theorem 21 | passed |
| thm22.py | Lemma 20 (904 systems; control), the subspace table in its proof, the case count of Corollary 13 | passed |
| plane_search.py | Lemmas 21 and 22; M(1) = 1 and M(2) = 2 exactly (201 systems); 864 systems with t = 3 | passed |
| normal_form.py | Lemma 23(a), (c), (d); the normal form on every system with t <= 2, and with t = 3 and dim C <= 2 | passed (new in 1.7.6) |
| nf_pencil.py | Example 1, Lemma 24, Proposition 21 (anisotropic systems) | passed (new in 1.7.6) |
| m3_core.py | Lemma 25, Theorem 23 (a)-(c), the systems left by Theorem 23, the count of 22 in the Remark | passed (new in 1.7.6) |
| m3_exact.py | Lemma 26, Theorem 24 (t <= 4), Proposition 22(b), the case count of Corollary 14 | passed (new in 1.7.7) |
| m4_irred.py | Lemmas 27 and 28; anisotropic systems with t = 4 over irreducible spaces | unit tests passed; full run queued (new in 1.7.8) |

Proved by hand only: Proposition 14, Lemma 8, Lemma 10, Proposition 16, Lemmas 11, 12 and 14, the
uniqueness claim in Proposition 10, the group-theoretic steps of Proposition 17, Lemma 18,
Theorems 19 to 22, Corollaries 12 to 14 and Proposition 20, Lemma 21(b), the Remark after
Theorem 24 (except the count of 22 in (b), which is computed), Corollary 15, and (until the run of
m4_irred.py has been graded) Lemmas 27 and 28. Lemma 25, Theorem 23, Theorem 24, Proposition 22 and
Corollary 15 also use the computed Proposition 21. Two numbers come from full runs that are too slow
for the unit tests: the Gamma(3; 4, 4) slacks of Proposition 9 and the order-2048 group checks.

**Concordance (draft label in the code -> label here).** Theorem 9 / Cor 9 -> Theorem 9 /
Corollary 9; Prop 5 -> Proposition 5; Prop 6 -> Proposition 6; Cor 10 -> Corollary 10;
Theorem 36 -> Theorem 10; Lemma 34 -> Lemma 7; Theorem 25 -> Theorem 11; Theorems 27 and 29' and the
lam_r LP -> Theorem 12; Theorem 29 -> Theorem 13; Prop 28 -> Proposition 7; Prop 35 ->
Proposition 8; Prop 37 -> Proposition 9; Prop 30 -> Proposition 10; Prop 31' -> Proposition 11;
Lemma 33 -> Lemma 8; Prop 15 -> Proposition 12; Lemma 13 (with its case Lemma 11) -> Lemma 9;
Prop 12 -> Proposition 13; Prop 11' and Lemma 26 -> Proposition 14; Prop 14 -> Proposition 15;
Cor 15a -> Corollary 11; Theorem 16 -> Theorem 14; Lemma 17 -> Lemma 10; Theorem 19 -> Theorem 15;
Prop 18 -> Proposition 16; Lemma 20 -> Lemma 11; Lemma 21 -> Lemma 12; Lemma 22 -> Lemma 13;
Lemma 38a -> Lemma 14; Theorem 38 -> Theorem 16; Theorem 39 -> Theorem 17; Theorem 40 ->
Theorem 18. So `theorem19.py` checks Theorem 15 here; the new Theorem 19 of 1.7.1 is checked by
`case42.py`, Theorem 20 of 1.7.2 by `case33.py`, Lemma 19, Theorem 21 and Corollary 12 of 1.7.3 by
`thm21.py`, Lemma 20, Theorem 22 and Corollary 13 of 1.7.4 by `thm22.py`, and Lemmas 21 and 22 of
1.7.5 by `plane_search.py` (its docstring calls them "draft Lemma 21" and "draft Lemma 22", and
uses the system sigma = x_1 x_2, alpha = x_1 + x_2 as its example for M(1) = 1). The docstrings of
these five modules already use the labels of this file. In 1.7.6, `normal_form.py` checks Lemma 23
(its docstring still states the refuted conjecture as a question), `nf_pencil.py` checks Example 1,
Lemma 24 (its docstring calls it "draft Lemma 24") and Proposition 21, and `m3_core.py` uses the
labels of this file. In 1.7.7, `m3_exact.py` uses the labels of this file; its "Lemma 26" is the
Lemma 26 of section 14, not the old draft label mapped to Proposition 14 above. In 1.7.8,
`m4_irred.py` uses the labels of this file. The note `notes/normal-form-counterexample.md` is the
first write-up of Example 1 and Lemma 24.

## Sources for this file

- T. Tao, "Product set estimates for non-commutative groups", Combinatorica 28 (2008);
  arXiv math/0601431.
- N. Gill, N. Lifshitz, L. Pyber, E. Szabo, "Initiating the proof of the Liebeck-Nikolov-Shalev
  conjecture", arXiv 2408.07800.
- S. Guerboussa, arXiv 1404.3621 (Lemma 2.10, citing Xu).
- M. Xu, Bull. Austral. Math. Soc. 36 (1987) 1-10 (not read by us; see Theorem 14).
- J. Gonzalez-Sanchez, T. S. Weigel, arXiv 0905.4513 (Theorem C).
- Z. Janko, J. Algebra 291 (2005) 505-533 (2-groups with three involutions; not read by us).
- G. Higman, "Suzuki 2-groups", Illinois J. Math. 7 (1963).
- D. A. Craven, A. Glesser, "Fusion systems on small p-groups", arXiv 1007.1639.
- N. Alon, B. Bukh, B. Sudakov, arXiv 0711.1604 (the universal set problem).
- V. Bovdi, M. Dokuchaev, "Group algebras whose involutory units commute", arXiv math/0009003
  (section 2 cites Blackburn's bound for exponent 4).
- B. Huppert, N. Blackburn, Finite Groups II, Springer, Theorem VIII.5.4 (not read by us).
- J. Pakianathan, E. Yalcin, "Quadratic maps and Bockstein closed group extensions",
  arXiv math/0606374 (abstract read; see the prior-work note of section 14).
- C. de Seguins Pazzis, "Primitive spaces of matrices with upper rank two over the field with two
  elements", arXiv 1405.1575 (abstract read; see the note after Corollary 15).

## Licence

Text CC BY 4.0; code Apache-2.0 (see LICENSE). By MV2 of Munim, Inc.; researched and written with
AI agents working in his name.
