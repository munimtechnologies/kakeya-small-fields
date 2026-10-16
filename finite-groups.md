# Cube translates in finite groups: partial families, and 2-groups with central involutions

By MV2 of Munim, Inc. Part of kakeya-small-fields version 1.7.2, 2026-10-16. This file holds
sections 13 and 14 of the README (https://github.com/munimtechnologies/kakeya-small-fields). It
was researched and written with AI agents working in MV2's name. Every statement is proved below,
and most are also checked by exact finite computations (the table at the end says which). **No
human mathematician has checked these proofs.** If you find an error, or find that a result is
already known, please open an issue. Text CC BY 4.0, code Apache-2.0.

Numbering continues from the README: version 1.6 ends with Proposition 4, Lemma 6, Theorem 8 and
Corollary 8, so this file starts at Theorem 9, Lemma 7, Proposition 5 and Corollary 9.

Version 1.7.2 adds Lemma 17, Proposition 19 and Theorem 20 to section 14. They settle the case
Z_4^3 x Z_2^3. Version 1.7.1 added Lemmas 15 and 16, Propositions 17 and 18 and Theorem 19, which
settle Z_4^4 x Z_2^2. README sections 14 and 15 still describe 1.7; where they differ, this file is
the current statement.

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
as after Proposition 18.

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

In general, for b >= 2 and s = 0, Proposition 19 gives n_0 <= a + 2b - dim S whenever
r >= ab - b + 1, and Lemma 17 gives r <= ab - 1 when a <= b and dim S >= 1. This is not enough
for the next cases. `cube_groups/case33.py` lists the cases the tools leave open, for example
s = 0, dim S = 2, r = 8 for (5, 2) (n <= 17, need 16); s = 0, r = 9 for (4, 3) (n <= 19, need 17);
and s = 1, r = 7 for (3, 4) (n <= 19, need 18).

*Status of Theorems 16 to 20.* They are proved by hand above. The full runs of
`cube_groups/z4degree.py` (Theorem 16: 6 of 6 groups consistent, both controls as predicted) and
`cube_groups/z4z2.py` (Theorem 17: 10 of 10 groups consistent, 4 of them with rank Q > 0, and the
control with a non-central involution fails as predicted) passed on 2026-10-16.
`cube_groups/hommap.py` (the lemma in Theorem 18) and `cube_groups/case42.py` (the linear-algebra
steps of Lemmas 15 and 16 and Proposition 18 with its polar-only control, the counting step of
Proposition 17, and a table of Lam(W) in codimension 2) passed their unit tests when they were
committed; their full runs are queued. `cube_groups/case33.py` (new in 1.7.2) checks
Proposition 19 over every W of codimension <= b - 1 for nine pairs (a, b), up to (3, 3) and (2, 4),
with both controls; the linear core of Lemma 17; and the case count of Theorem 20 (the tools of
1.7.1 alone leave (3, 3) open, and with Proposition 19 and Lemma 17 the largest bound is 15). It is
committed separately, only if its unit tests pass, and its full run is queued. The group-theoretic
steps of Proposition 17 and Theorems 19 and 20 are checked by hand only.

**Where the question stands.** Proved: e <= 2; class 2 (Theorem 15); e = 3 with x -> x^4 a
homomorphism; groups with a unique-involution series of length k; a self-centralising normal
Z_4^k; a self-centralising normal Z_4^a x Z_2^b when a <= 2, when b <= 1, when
ab - s(b-1) <= a + b, when dim span sigma(H) <= 1 and a + b >= 3, when rank Q = ab and a <= b,
whenever (a - 1)(b - 1) <= 3 (including (3, 2) and (4, 2)), and for (3, 3). Computed: true on every
subgroup of Q_16, Q_32, Q_8^2 and Q_16 x Q_8, and of nine class-2 groups up to order 256. An exact
search over all 324 conjugacy classes of 7-dimensional subspaces of M_3(F_2) found no
counterexample with A ~ Z_4^3, as Theorem 16 predicts. Open: Z_4^a x Z_2^b with b = 2 and a >= 5,
or with a, b >= 3 other than (3, 3), starting with (5, 2), (4, 3) and (3, 4); homocyclic
Z_(2^m)^k with m >= 3; the general case. A classification of the 2-groups with exactly three
involutions (k = 2) is in Janko, J. Algebra 291 (2005) 505-533. We could not read it, so the case
k = 2 is not claimed.

*Prior work.* Searches on 2026-10-15 and 2026-10-16 found no statement of this question. The
literature's "2-central" means Omega_2 <= Z, which is a stronger hypothesis. Higman's Suzuki
2-groups (1963) are the case e = 2 in a special setting. The tools (quadratic maps, Chevalley-
Warning, determinants of degree-bounded matrices) are standard, so a specialist may know these
bounds. Please open an issue if so.

## Verification table

Every module below is in `cube_groups/` (pure Python, no dependencies). `python -m unittest -v` at
the top of the repository runs all their unit tests, and running a module as a script
(`python cube_groups/<module>.py --help`) runs its full check. The full runs were done in a sealed container on
2026-10-15 and 2026-10-16. The module docstrings use the labels of our working drafts; the
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
| hommap.py | the lemma in Theorem 18 | unit tests passed; full run queued |
| case42.py | Lemmas 15 and 16, Proposition 18, the counting step of Proposition 17 | unit tests passed; full run queued |
| case33.py | Proposition 19 (two controls), the linear core of Lemma 17, the case count of Theorem 20 | queued (new in 1.7.2) |

Proved by hand only: Proposition 14, Lemma 8, Lemma 10, Proposition 16, Lemmas 11, 12 and 14, the
uniqueness claim in Proposition 10, the group-theoretic steps of Proposition 17 and Theorems 19 and
20, and (until their runs finish) Theorems 18 to 20 and Propositions 18 and 19. Two numbers come from
full runs that are too slow for the unit tests: the Gamma(3; 4, 4) slacks of Proposition 9 and the
order-2048 group checks.

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
`case42.py`, and Theorem 20 of 1.7.2 by `case33.py`. The docstrings of those two modules already use
the labels of this file.

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

## Licence

Text CC BY 4.0; code Apache-2.0 (see LICENSE). By MV2 of Munim, Inc.; researched and written with
AI agents working in his name.
