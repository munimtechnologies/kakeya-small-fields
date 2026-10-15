# Smaller Kakeya sets over small finite fields

**New upper bound: lim K(n, q)^(1/n) <= q * 2^(-(q-1)/q) for every finite field F_q.**
**An exact entropy formula for that limit (1.1). Permutation-invariant Kakeya sets over F_3 have
growth base exactly 2 (new in 1.2). Maps that respect a linear quotient cannot beat the bound
(new in 1.2). An exhaustive search over all 9^9 maps on F_3^2 shows that blocks of size 2 do not
beat it over F_3 (new in 1.3). Kakeya sets of higher rank: for every q >= 3 and r >= 2, sets
containing a translate of every r-dimensional subspace can be smaller than the bounds of Kopparty,
Lev, Saraf and Sudan, and their growth base is q - q^(2-r) + O(q^(1-r) log q) (new in 1.4).
Over F_2 the growth base of Kakeya sets of rank r is exactly 2^(1 - 2^(-r)) for every r: every
rank-2 Kakeya set in F_2^n has at least 2^(3n/4) points, which answers the case q = r = 2 that
Kopparty, Lev, Saraf and Sudan singled out (new in 1.5).**

By MV2 of Munim, Inc. Version 1.5, 2026-10-15. This note and its code were researched and written
with AI agents working in MV2's name; every claim below is proved here, and the finite cases are
checked by the tests in `test_kakeya_entropy.py`, `test_search_h2.py`, `test_structure.py`,
`test_exact_h2.py`, `test_higher_rank.py` and `test_f2_rank.py`. Text CC BY 4.0, code Apache-2.0.

## 1. Summary

A Kakeya set in F_q^n contains a full line {a + t d : t in F_q} in every direction d. Let K(n, q)
be the least size of one. Products of Kakeya sets are Kakeya sets, so the limit

    beta_q = lim K(n, q)^(1/n) = inf K(n, q)^(1/n)

exists. Kopparty, Lev, Saraf and Sudan (KLSS, 2010) asked for it, calling q = 3 "most intriguing".
We prove

    beta_q <= q * 2^(-(q-1)/q) = (q/2) * 2^(1/q)    for every prime power q,

with an explicit set. For every q >= 4 this is below every upper bound we could find in the
literature. For q = 3 it equals the bound KLSS proved with randomly chosen linear maps (1.8899) and
gives the first explicit construction we know of with that base. The bound is within a factor
2^(1/q) (1 - 1/(2q)) = 1 + 0.19/q + O(1/q^2) of the lower bound q^2/(2q - 1).

| q | lower bound q^2/(2q-1) | best upper bound we found before | new upper bound |
|---|---|---|---|
| 2 | 1.3333 | 1.4142 = sqrt 2 (exact) | 1.4142 |
| 3 | 1.8 | 1.8899 (KLSS Th. 8, random); 2 explicit | **1.8899, explicit** |
| 4 | 2.2857 | 2.8284 (KLSS Th. 8, random); 3 explicit | **2.3784** |
| 5 | 2.7778 | 3 (KLSS Th. 6) | **2.8717** |
| 7 | 3.7692 | 4 (KLSS Th. 6) | **3.8643** |
| 8 | 4.2667 | 6.3321 (Kyureghyan-Muller-Wang Th. 3.2) | **4.3620** |
| 9 | 4.7647 | 5 (KLSS Th. 6) | **4.8603** |
| 16 | 8.2581 | 10 (Kyureghyan-Muller-Wang Th. 2.2) | **8.3542** |

(`python kakeya_entropy.py table` prints this table; the tests check every number in it.)

The idea in one sentence: KLSS build Kakeya sets from a function f with small image sets
{f(x) + t x : x in F_q} and pay for the *largest* of the q images; cutting the coordinates into
blocks and shifting the line's parameter separately on each block lets us pay for the *average*
of their *entropies* instead.

Section 6 shows that this averaging loses nothing. For a map P : F_q^k -> F_q^k let
h(P) = (1/q) sum over t of H(P(X) + t X), with X uniform on F_q^k, and let h_k be the least h(P).
Then

    beta_q = inf over k of 2^(h_k / k)        (Theorem 2),

and h_1 = log2 q - (q-1)/q, which is the bound above. So the bound is the true value of beta_q
exactly when h_k = k h_1 for every k. A single map P on F_q^k with h(P) < k h_1, a finite object
that a computer can check, would give an explicit Kakeya construction beating it.

The rest of the note narrows down where such a map could be, and then turns to flats:

- **Section 7 (Theorem 3, completed in 1.2).** A Kakeya set invariant under permuting coordinates
  never beats the bound, and over F_3 the best such sets have base exactly 2. Theorem 1 needs its
  block structure.
- **Section 8 (Theorem 4, new in 1.2).** If P respects a linear quotient (P(x + w) - P(x) lies in a
  subspace W whenever w does), then h(P) >= h_(k-l) + h_l. So a map that beats the bound must
  respect no proper subspace; affine maps never beat it.
- **Section 9 (new in 1.3).** For q = 3 and k = 2 the question is settled by an exhaustive search:
  no map on F_3^2 beats the coordinatewise squares, so h_2 = 2 h_1 over F_3. The first open case
  over F_3 is now k = 3.
- **Section 10 (new in 1.4).** The same averaging works for Kakeya sets of rank r (a translate of
  every r-dimensional subspace). Two simple witnesses, the square of one coordinate and the norm
  form of F_(q^2), beat both upper bounds of KLSS for every q >= 3 and r >= 2, and together with
  the KLSS lower bound they pin the growth base down to q - q^(2-r) + O(q^(1-r) log q). For r = 2
  it is q - 1 + O((log q)/q); the bounds known before left it anywhere between q - 1 + O(1/q) and
  about q - (ln q)/q.
- **Section 11 (Theorem 7, new in 1.5).** Over F_2 a short entropy argument gives
  |K| >= 2^((1 - 2^(-r)) n) for every Kakeya set K of rank r in F_2^n. The universal-set
  construction of KLSS has size below 2^((1 - 2^(-r)) n + r + 1), so the growth base for q = 2 is
  exactly 2^(1 - 2^(-r)) for every r. KLSS asked for this limit "even for just one particular pair
  (q, r) != (2, 1)", and called the case q = r = 2 non-trivial.

## 2. Background and prior bounds

- **Lower bounds.** KLSS (Theorem 1 with r = 1) and Bukh-Chao (2021) give
  |K| >= q^n / (2 - 1/q)^(n-1), so beta_q >= q^2/(2q - 1).
- **KLSS Theorem 6** (built from f(x) = x^2 for odd q): |K| < 2(1 + 1/(q-1)) ((q+1)/2)^n for odd q,
  base (q + 1)/2; for even q, base (2q + 1)/3 or 2(q + sqrt q + 1)/3.
- **KLSS Theorem 8**: |K| < (q / 2^(2/q))^(n + O(sqrt n)), proved by moving one set by n randomly
  chosen linear automorphisms. KLSS note that it beats Theorem 6 only for q in {3, 4, 8}.
- **Kyureghyan, Muller and Wang (2013)**: better functions f for even q: base (q + sqrt q)/2 when q
  is an even power of 2 (equal to 3 at q = 4) and (5q + 2 sqrt q + 5)/8 when q is an odd power of 2.
- **q = 2**: a Kakeya set of F_2^n is a difference basis of the group, and beta_2 = sqrt 2 exactly.
- The Dvir and Saraf-Sudan constructions of size about q^n / 2^(n-1) are statements for fixed n and
  large q; for fixed q they have base (q + 1)/2 again.

We searched the web and arXiv for a better bound with q fixed and n growing, and for an entropy
formula like Theorem 2 (searches of 2026-10-14, including later work on these constructions, the
2025 Kakeya survey and Tao's 2025 Nikodym paper) and found none. The 2025 AlphaEvolve Kakeya
results (Georgiev, Gomez-Serrano, Tao, Wagner) are for fixed dimension 3 to 5 and large q. If an
earlier proof of these results exists, we would like to cite it; please open an issue.

## 3. The construction

Fix q and integers m, r >= 1, and let n = r m. Cut x in F_q^n into r blocks x^(1), ..., x^(r) of
length m. For y in F_q^m let N(y) be the number of vectors with the same symbol counts as y (a
multinomial coefficient), and put

    w(x) = log2 N(x^(1)) + ... + log2 N(x^(r)),
    K = { x in F_q^n : w(x) <= T },    T = r m c_q + m log2(q) sqrt(r ln q),
    c_q = log2 q - (q - 1)/q.

Membership is decided by counting symbols, so K is explicit.

**Theorem 1.** K is a Kakeya set, and
|K| <= C(m + q - 1, q - 1)^r * 2^T. Taking m about n^(1/3) and r about n^(2/3),

    K(n, q) <= (q * 2^(-(q-1)/q))^(n + O_q(n^(2/3) log n)),

so beta_q <= q * 2^(-(q-1)/q).

The size bound is immediate: K is a union of at most C(m + q - 1, q - 1)^r tuples of composition
classes, each with at most 2^T points. The rest of this section proves that K is Kakeya.

**Lines.** Let g_t(x) = x^2 + t x on F_q, applied to vectors coordinatewise. For a nonzero
direction d with blocks u_j = d^(j), choose shifts s_1, ..., s_r in F_q and let a be the point
whose block j is u_j^2 + s_j u_j. Then block j of a + t d is g_(s_j + t)(u_j), so the line through
a in direction d has

    w(a + t d) = sum over j of v_j(s_j + t),    v_j(t) = log2 N(g_t(u_j)).

**Lemma 1 (one block).** If u in F_q^m has symbol distribution tau, then
v(t) <= m H(g_t # tau), where H is the Shannon entropy in bits and g_t # tau the image
distribution. (N(y) <= 2^(m H) for every vector y of length m.)

**Lemma 2 (entropy).** For every probability distribution tau on F_q,

    sum over t in F_q of H(g_t # tau) <= q log2 q - (q - 1),

with equality at the uniform distribution.

*Proof.* The left side is concave in tau, because each g_t # tau is linear in tau and H is concave.
It is invariant under translations tau(x) -> tau(x - b). For odd q, the fibres of g_t are the pairs
{x, -t - x}, and translating by b turns them into the fibres of g_(t + 2b); 2b runs over F_q.
In characteristic 2, g_0 = x^2 is a bijection, and for t != 0 the fibres of g_t are the pairs
{x, x + t}, which translation preserves. Averaging the q translates of tau gives the uniform
distribution, so by concavity the uniform distribution is a maximum. There, for odd q, each g_t has
(q - 1)/2 fibres of size 2 and one of size 1, so H = log2 q - (q - 1)/q; in characteristic 2, g_0
has entropy log2 q and the other q - 1 maps have entropy log2 q - 1. Both sum to
q log2 q - (q - 1). QED

**Lemma 3 (balancing).** Choose the shifts s_j independently and uniformly at random. For fixed t
the terms v_j(s_j + t) are independent, lie in [0, M] with M = m log2 q, and their mean is
(1/q) sum_t v_j(t) <= m c_q (Lemmas 1 and 2). By Hoeffding's inequality,
P(w(a + t d) > r m c_q + lambda) <= exp(-2 lambda^2 / (r M^2)), which is 1/q^2 for
lambda = M sqrt(r ln q). A union bound over the q values of t leaves probability at least 1 - 1/q
that every point of the line has w <= T. So some choice of shifts puts the whole line in K. QED

This proves Theorem 1. Only the *existence* of the shifts uses probability; the set K itself is
explicit, and good shifts can be found deterministically (by the method of conditional
expectations, or by the exact rule below when q = 3).

**Why it works.** KLSS's Theorem 6 uses the same lines (for odd q, f(x) = x^2) but must contain every
point of every such line in a single symmetric set, so it pays for the largest image
|{f(x) + t x}|. Here the q points of a line take turns being cheap on different blocks, so each
point pays the average over t, and the composition classes make it the entropy rather than the
support size. At the uniform distribution the average is log2 q - (q - 1)/q, against
log2 ((q + 1)/2) for Theorem 6 and log2 q - 2/q for Theorem 8. These coincide only at q = 3.

## 4. This is the limit of one-coordinate witnesses

For *any* function f : F_q -> F_q and the uniform distribution,
sum over t of H(f(x) + t x) >= q log2 q - (q - 1). Two points x != y collide under f(x) + t x for
exactly one t, so the C(q, 2) pairs are shared out among the q maps. A fibre of size s lowers the
entropy by (s log2 s)/q and uses C(s, 2) pairs, and s log2 s <= s(s - 1) = 2 C(s, 2) with equality
only for s <= 2. So the total reduction is at most q - 1, and it is reached exactly when all fibres
have size at most 2, as for f = x^2. (The tests check this for every f when q <= 5.) Going below
q * 2^(-(q-1)/q) therefore needs witnesses that are not of the form "one function per coordinate".
Sections 6 to 9 show what such witnesses must do.

## 5. q = 3 without probability

For q = 3, a block u with z zeros, p ones and k twos gives the three points of its line two-symbol
vectors with class sizes C(m, z), C(m, p) and C(m, k). Using -x^2 as well as x^2 and the three
shifts, every one of the six orders of these three numbers is available. Process the blocks in turn
and give the largest number to the point with the smallest product so far, the middle one to the
middle point and the smallest to the largest. Write e_0 >= e_1 >= e_2 for the logarithms of the
three numbers and l_0 <= l_1 <= l_2 for the points' logarithmic loads before the step. Every
difference between new loads is at most max(l_2 - l_0, e_0 - e_2), so the spread of the loads never
exceeds M = log2 C(m, floor(m/2)), and the largest load is at most the average plus 2M/3. With
Q(m) = max over a + b + c = m of C(m, a) C(m, b) C(m, c) (the balanced split, by log-concavity),
this gives the explicit Kakeya set

    K3 = { x in F_3^(rm) : every block uses at most two symbols and
           (product of the blocks' class sizes)^3 <= Q(m)^r * C(m, floor(m/2))^2 },

    |K3| <= (3m)^r * Q(m)^(r/3) * C(m, floor(m/2))^(2/3) <= (3m)^r * 4^(m/3) * (3 / 4^(1/3))^(rm),

so K(n, 3) <= (3 / 4^(1/3))^(n + O(sqrt(n log n))). `k3_witness` computes the line for any direction.
The convergence is slow. At m = 300, r = 100 (n = 30,000) the bound gives base below 2^0.95 = 1.932.
That already beats the explicit 189 * 1.9626^n of kakeya-conjecture v1.2.0, which this note
supersedes asymptotically. At m = r = 3000 the base is below 2^0.925 = 1.8987.

## 6. An exact entropy formula for beta_q (new in 1.1)

For k >= 1 and any map P : F_q^k -> F_q^k, let X be uniform on F_q^k and

    h(P) = (1/q) * sum over t in F_q of H(P(X) + t X),        h_k = min over P of h(P).

Geometrically, P picks one line {(t, P(x) + t x) : t in F_q} in each of the q^k non-vertical
directions (1, x) of F_q^(k+1), and h(P) is the average, over the q horizontal slices
{t} x F_q^k, of the entropy of the point where a randomly chosen one of these lines meets the
slice. Equivalently, with S(P) = sum over t and over the fibres of x -> P(x) + t x of s log2 s,

    h(P) = k log2 q - S(P) / q^(k+1).

**Theorem 2.** For every prime power q,

    beta_q = lim over k of 2^(h_k / k) = inf over k of 2^(h_k / k),   and   h_1 = log2 q - (q-1)/q.

*Proof.* (i) h_(k+l) <= h_k + h_l: use P on the first k coordinates and P' on the last l; X splits
into independent uniform parts, so the entropies add. By Fekete's lemma the limit exists and equals
the infimum.

(ii) h_k <= log2 K(k, q). Let K0 be a Kakeya set of F_q^k. For x != 0 let P(x) be a point with
P(x) + t x in K0 for every t, and let P(0) be any point of K0. Every P(X) + t X lies in K0, so each
entropy is at most log2 |K0|. Hence inf 2^(h_k/k) <= inf K(k, q)^(1/k) = beta_q.

(iii) beta_q <= 2^(h_k / k). For a distribution tau on F_q^k let
phi(tau) = min over P of (1/q) sum_t H(P(Y) + t Y) with Y ~ tau. For fixed P each term is concave
in tau (the law of P(Y) + t Y is linear in tau), and a minimum of concave functions is concave.
phi is translation invariant: if Y' = Y + b, then P'(y) = P(y - b) gives
P'(Y') + t Y' = P(Y) + t Y + t b, a translate. Averaging the q^k translates of tau gives the uniform
distribution, so phi(tau) <= phi(uniform) = h_k for every tau. Now repeat section 3 over the
alphabet F_q^k. A point of F_q^n, n = k m r, is r blocks of m letters, each letter in F_q^k; N(y)
counts the words with the same letter counts as y, and

    K = { x : sum over j of log2 N(x^(j)) <= T },    T = r m h_k + m k log2(q) sqrt(r ln q).

For a direction d whose block j is a word u_j with letter distribution tau_j, choose P_j attaining
phi(tau_j), choose shifts s_j, and let a have the letter P_j(u) + s_j u wherever block j of d has
the letter u. Block j of a + t d has the letters P_j(u) + (s_j + t) u, so its letter distribution
is the law of P_j(Y) + (s_j + t) Y with Y ~ tau_j, and its cost log2 N is at most m times that
entropy. Averaged over a uniform shift s_j this is at most m phi(tau_j) <= m h_k. Hoeffding's
inequality, exactly as in Lemma 3 with M = m k log2 q, gives shifts that put the whole line in K,
and |K| <= C(m + q^k - 1, q^k - 1)^r 2^T. Taking m about n^(1/3) gives beta_q <= 2^(h_k / k).

(iv) Section 4 shows h(P) >= log2 q - (q-1)/q for every P on F_q, and P(x) = x^2 attains it.

By (iii), beta_q <= inf 2^(h_k/k), and by (ii) the infimum is at most beta_q. QED

**Corollary 1.** beta_q = q * 2^(-(q-1)/q) if and only if h_k = k h_1 for every k. By (i),
h_k <= k h_1 always; if h_k < k h_1 for one k, then beta_q <= 2^(h_k/k) is a better bound. So one
map P on F_q^k with S(P) > k (q - 1) q^k, which is the same as h(P) < k h_1, gives an explicit
Kakeya construction below q * 2^(-(q-1)/q). For q = 2 the bound is the truth (beta_2 = sqrt 2), so
h_k = k/2 for every k; the tests confirm h_2 = 1 over all 256 maps on F_2^2.

**Corollary 2.** k log2(q^2/(2q - 1)) <= h_k <= k (log2 q - (q-1)/q). The left side is the
known lower bound for beta_q, read through Theorem 2. So for every map P on F_q^k,
S(P) <= q^(k+1) (k log2 q - k log2(q^2/(2q-1))); `score_ceiling` computes this.

The formula turns the question "what is beta_q?" into a sequence of finite optimisation problems,
one for each k, with the k = 1 problem solved exactly (section 4). It does not by itself say
whether h_k/k ever drops below h_1.

## 7. Sets symmetric under permuting coordinates (completed in 1.2)

Most explicit constructions are unions of composition classes: a point's membership depends only
on how often each symbol occurs. Theorem 1's set is not: it is symmetric only within blocks.

**Theorem 3.** (a) If K in F_q^n is a Kakeya set that is invariant under all permutations of the
coordinates and q divides n, then |K| >= (q * 2^(-(q-1)/q))^n / (n + 1)^q.

(b) For q = 3, every permutation-invariant Kakeya set in F_3^n has |K| >= 2^n / (n + 1)^3 when n
is even and |K| >= 2^(n-1) / n^3 when n is odd. The permutation-invariant set of points that use at
most two of the three symbols is a Kakeya set with 3 * 2^n - 3 points.

So the best growth base of permutation-invariant Kakeya sets is never below q * 2^(-(q-1)/q), and
over F_3 it is **exactly 2**, against 1.8899 for Theorem 1's block construction. Version 1.1 proved
only "strictly above 1.8899" and conjectured 2. (Part (a) is far from sharp for q = 2: a union of
Hamming-weight levels needs about 2^(0.81 n) points to contain every difference, while
beta_2 = sqrt 2.)

*Proof of (a).* Let u be a direction in which each symbol occurs n/q times, and let a + t u be a
line in K. Let pi be the joint distribution of the pairs (u_i, a_i) over the n coordinates; its
first marginal is uniform. The symbol distribution of a + t u is the law of Y + t X for
(X, Y) ~ pi. K contains the whole class of a + t u, which has at least 2^(n H(Y + t X)) / (n + 1)^q
points. Write pi(x, y) = kappa(y | x) / q and expand it as a mixture of functions:
pi = sum over f of w_f pi_f, where pi_f is the law of (X, f(X)) and
w_f = product over x of kappa(f(x) | x). The law of Y + t X is the same mixture of the laws of
f(X) + t X, so by concavity and section 4,

    sum over t of H(Y + t X) >= sum over f of w_f * sum over t of H(f(X) + t X) >= q log2 q - (q - 1).

Some t therefore has H(Y + t X) >= c_q. QED

*Proof of (b).* For even n take u with n/2 zeros and n/2 ones, and a line a + t u in K. If the
symbols of a are distributed as k0 where u is 0 and as k1 where u is 1, then point t of the line
has symbol distribution

    M_t(z) = (k0(z) + k1(z - t)) / 2.

K contains the whole class of a + t u, which has at least 2^(n H(M_t)) / (n + 1)^3 points, so
Lemma 4 below gives |K| >= 2^n / (n + 1)^3. For odd n, let K' be the set of y in F_3^(n-1) with
(y, c) in K for some c. A line of K in direction (d', 0) gives a line of K' in direction d', so K'
is a permutation-invariant Kakeya set of F_3^(n-1) with |K'| <= |K|. The two-symbol set is Kakeya
because g_t(u) = u^2 + t u uses at most two symbols (g_t has a fibre of size 2 on F_3), and it has
3 (2^n - 2) + 3 points. QED

**Lemma 4.** For all probability distributions k0, k1 on F_3, max over t of H(M_t) >= 1, with
equality when k0 and k1 are point masses.

*Proof.* Point masses give one slice of entropy 0 and two of entropy 1. Suppose H(M_t) < 1 for
t = 0, 1, 2. A distribution whose largest mass is at most 1/2 has entropy at least 1, so each M_t
has a symbol z_t with M_t(z_t) > 1/2, that is,

    (*)  k0(z_t) + k1(z_t - t) > 1.

(i) *Exactly two z_t are equal*, say z_s = z_t = z != z_u. Then z - s != z - t. If z_u - u is the
third symbol, the three k1 values in (*) are at different symbols, and adding the three
inequalities gives 2 k0(z) + k0(z_u) + 1 > 3, impossible since k0(z) + k0(z_u) <= 1. If z_u - u
equals z - s, adding (*) for t and for u gives k0(z) + k0(z_u) + k1(z - t) + k1(z - s) > 2,
impossible because both pairs are masses at different symbols. The case z_u - u = z - t is the same.

(ii) *The z_t are all different.* Then the k0 terms of (*) add up to 1, so the k1 terms add up to
more than 2. That forces z_t - t to be the same symbol s for all t: if two of the z_t - t differ,
the k1 terms add up to at most k1(s1) + (k1(s1) + k1(s2)) <= 2. Now swap the roles of k0 and k1:
with k0' = k1 and k1' = k0 the new slices are M'_t(z) = M_(-t)(z - t), translates of the old ones,
and every M'_t has its large mass at the same symbol s. So this case reduces to case (iii).

(iii) *All z_t are equal.* Translating k0 and k1 by the same amount translates every M_t, so we may
take z_t = 0. Put alpha = k0(0) and g = min over s of k1(s), so g <= 1/3. By (*),
alpha + k1(-t) > 1 for every t; adding the three, 3 alpha + 1 > 3, so alpha > 2/3, and g > 1 - alpha.
Take t with k1(-t) = g. Then M_t(0) = (alpha + g)/2, and each of the two other masses of M_t is at
least k1(z - t)/2 >= g/2. With the mass at 0 fixed, the entropy is smallest when the rest is split
as unevenly as allowed, so

    H(M_t) >= F(alpha, g) = H( (alpha + g)/2, (2 - alpha - 2g)/2, g/2 ).

F is concave in (alpha, g) (the entropy of an affine function), so on the triangle
2/3 <= alpha <= 1, 1 - alpha <= g <= 1/3 it is smallest at a vertex: F(1, 0) = H(1/2, 1/2, 0) = 1,
F(1, 1/3) = H(2/3, 1/6, 1/6) = 1.2516 and F(2/3, 1/3) = H(1/2, 1/3, 1/6) = 1.4591. So
H(M_t) >= 1, a contradiction. QED

`test_structure.py` checks Lemma 4 on a grid of 8,281 pairs (k0, k1), on 20,000 random pairs and on
5,000 pairs near the point masses, checks the bound F on the triangle and on the actual slices of
case (iii), and checks the two-symbol set up to F_3^4.

## 8. Maps that respect a linear quotient cannot beat the bound (new in 1.2)

Theorem 2 reduces the question to maps P : F_q^k -> F_q^k. This section rules out a large,
natural class of them.

**Theorem 4.** Let W be a subspace of F_q^k of dimension l, 0 < l < k, and suppose
P(x + w) - P(x) lies in W for every x in F_q^k and every w in W. Then

    h(P) >= h_(k-l) + h_l.

*Proof.* Write Y_t = P(X) + t X. Let pi be the quotient map F_q^k -> F_q^k / W, a space of
dimension k - l. By the hypothesis, P induces a map Pbar on the quotient with
Pbar(pi x) = pi P(x), and pi Y_t = Pbar(pi X) + t pi X with pi X uniform. So
sum over t of H(pi Y_t) >= q h_(k-l). Next, H(Y_t) = H(pi Y_t) + H(Y_t | pi Y_t), and pi Y_t is a
function of pi X, so H(Y_t | pi Y_t) >= H(Y_t | pi X). Given pi X = c, fix a point x_c with
pi x_c = c. Then X = x_c + V with V uniform on W, and

    Y_t = (P(x_c) + t x_c) + Q_c(V) + t V,    Q_c(v) = P(x_c + v) - P(x_c),

where Q_c maps W to W. The first bracket is a constant, so
sum over t of H(Y_t | pi X = c) >= q h_l. Averaging over c and adding,
sum over t of H(Y_t) >= q (h_(k-l) + h_l). QED

In coordinates with W spanned by the first l unit vectors, the hypothesis says that the last
k - l coordinates of P(x) depend only on the last k - l coordinates of x: P is block-triangular.
This includes every coordinatewise map, and the coordinatewise squares (which give equality) in
particular.

- **k = 2.** Since h_1 = log2 q - (q-1)/q (section 4), every map on F_q^2 that respects a line W
  has h(P) >= 2 h_1. A map on F_q^2 that beats Theorem 1 must respect no line: for each of the
  q + 1 lines W there must be x and w in W with P(x + w) - P(x) outside W.
- **Induction.** If h_j = j h_1 for every j < k, then no map on F_q^k that respects a proper nonzero
  subspace beats k h_1. With section 9, this applies to q = 3 and k = 3.

**Corollary 3 (affine maps).** If P(x) = A x + b for a k x k matrix A over F_q, then
h(P) >= k (q - 1) log2(q) / q, which is at least k h_1, with equality only for q = 2.
Equivalently S(P) <= k q^k log2 q, with equality at A = 0.

*Proof.* Y_t = (A + t I) X + b is uniform on a coset of the image of A + t I, so
H(Y_t) = (k - dim ker(A + t I)) log2 q. The kernels are eigenspaces of A for the different
eigenvalues -t, so their dimensions add up to at most k, and
sum over t of H(Y_t) >= (q - 1) k log2 q. Finally (q - 1) log2(q) / q >= log2 q - (q - 1)/q
is the inequality q - 1 >= log2 q. QED

`test_structure.py` checks Theorem 4 on random block-triangular maps for (q, k) = (2, 2), (3, 2)
and (5, 2), and Corollary 3 on all 81 matrices over F_3 and on random affine maps over F_5^2,
F_3^3 and F_2^3.

## 9. Maps on F_3^2: blocks of size 2 do not beat the bound over F_3 (new in 1.3)

By Corollary 1, beta_3 < 1.8899 could come from one map P : F_3^2 -> F_3^2 with S(P) > 36: nine
lines in the nine non-vertical directions of F_3^3 whose three horizontal slices are more
concentrated, in total, than those of the coordinatewise squares (S = 36, each slice with fibres
of sizes 4, 2, 2 and 1). Corollary 2 caps S at 39.80.

**Result.** The largest value of S(P) over all 9^9 maps P : F_3^2 -> F_3^2 is exactly 36. So
h_2 = 2 h_1 for q = 3, and blocks of size 2 cannot improve Theorem 1 over F_3.

*Method.* `exact_h2.py` fixes P(0) = 0 (P -> P + c does not change S) and runs a branch and bound
over the 9^8 = 43,046,721 remaining maps. Each x gives the progression P(x), P(x) + x, P(x) + 2x,
one point per slice. The search chooses P(x) for x = 1, ..., 8 in turn and keeps, for each slice,
how many progressions pass through each point. Adding a point to a cell that already holds c
points raises S by D(c) = (c+1) log2(c+1) - c log2 c, and D increases with c. So r more
progressions can raise a slice whose fullest cell holds m points by at most
D(m) + ... + D(m + r - 1), and every branch whose bound falls below 36 is cut. Nothing with
S >= 36 is cut, so the search finds the exact maximum.

*Checks.* `test_exact_h2.py` runs the full search (pure Python). It also checks the branch and
bound against brute force on every map for (q, k) = (2, 1), (3, 1), (5, 1) and (2, 2), and on six
families of maps on F_3^2 with four or five values fixed (6,561 or 729 maps each). It checks it
against the theory for q = 2, k = 3, where the maximum must be 24, and recomputes the maximiser's
score with separate code. This version was committed only after that test passed. An independent
numpy search over the same 43 million maps (`search_h2.py exhaustive --q 3 --k 2`) is queued as a
second check, and we will report its result.

**What this does and does not say.** The value of beta_3 is still open between 1.8 and 1.8899.
Theorem 2 says it is below 1.8899 only if some k has h_k < k h_1, and this rules out k = 2. The
first open case over F_3 is k = 3: a map on F_3^3 with S(P) > 162 (the ceiling is 179.08). By
Theorem 4 and this result, such a map must respect no proper subspace of F_3^3. There are 27^26
maps with P(0) = 0, far too many for this search. For larger q the k = 2 case is still open:

| q | S of the squares = threshold | ceiling from the lower bound |
|---|---|---|
| 3 | 36 (now known to be the maximum) | 39.80 |
| 4 | 96 | 103.34 |
| 5 | 200 | 212.00 |

## 10. Kakeya sets of higher rank (new in 1.4)

A **Kakeya set of rank r** in F_q^n contains a translate of every r-dimensional subspace; rank 1
is the usual Kakeya set. Let K_r(n, q) be the least size of one (n >= r). If K1 and K2 have rank r,
so does K1 x K2: the projection of an r-dimensional subspace D of F_q^(n1+n2) to each factor lies
in an r-dimensional subspace of that factor, whose translate the factor contains, and the product
of the two translates contains a translate of D. So

    beta_(q,r) = lim K_r(n, q)^(1/n)

exists. KLSS (section 6 of their paper) note that for r >= 2 "there is no reason to believe" their
bounds are sharp, and ask for this limit for any single pair (q, r) other than (2, 1). Their
bounds for fixed q and growing n are

- lower (KLSS Theorem 1): beta_(q,r) >= q^(r+1) / (q^r + q - 1) = q / (1 + (q - 1) q^(-r));
- upper: beta_(q,r) <= q^(1 - q^(-r)) (Theorem 10, from a "universal" set) and
  beta_(q,r) <= q (1 - (q - delta_q) / (2 q^r))^(1/(r+1)) (Theorem 4; delta_q = 5/3 for q = 3,
  3 for odd q >= 5, 1 for even q).

In this section R is the number of blocks (it was called r in sections 3 and 6).

**Theorem 5.** For a function f : F_q^r -> F_q let

    Phi(f) = (1/q^r) * sum over t in F_q^r of H(f(U) + <t, U>),    U uniform on F_q^r.

Then beta_(q,r) <= 2^Phi(f).

*Proof.* Section 3 with columns in place of symbols. Let n = R m, cut F_q^n into R blocks of m
coordinates, and let K = { x : sum over j of log2 N(x^(j)) <= T } with
T = R m Phi(f) + m log2(q) sqrt(R r ln q). Let D be an r-dimensional subspace with basis
d_1, ..., d_r, and for each coordinate c let u_c = (d_1c, ..., d_rc) in F_q^r be its column. For
b_j and s_j in F_q^r, let a have coordinate f(u_c - b_j) + <s_j, u_c> for c in block j. The point
a + t_1 d_1 + ... + t_r d_r has coordinate f(u_c - b_j) + <s_j + t, u_c>, so the symbol
distribution of its block j is the law of f(Y - b_j) + <s_j + t, Y>, where Y is a uniformly chosen
column of block j. Write Phi_f(tau) for Phi computed with U ~ tau. Then f(Y - b) + <s, Y> is a
translate of f(Z) + <s, Z> with Z = Y - b, and the laws of Y - b average, over the q^r values of b,
to the uniform law. Phi_f is concave in tau, so some b_j makes the average over s of
H(f(Y - b_j) + <s, Y>) at most Phi(f). With that b_j, the cost log2 N of block j is at most m
times this entropy (Lemma 1), so its mean over a uniform shift s_j is at most m Phi(f). Hoeffding's
inequality with M = m log2 q and a union bound over the q^r points t, as in Lemma 3, give shifts
that put all of a + D in K. Finally |K| <= C(m + q - 1, q - 1)^R 2^T, and m about n^(1/3) gives
beta_(q,r) <= 2^Phi(f). QED

**Corollary 4 (three witnesses).**

- (a) f = 0. The slice t = 0 is constant and the others are uniform, so
  Phi = (1 - q^(-r)) log2 q. This is the base q^(1 - q^(-r)) of KLSS's Theorem 10.
- (b) f(u) = u_1^2. A slice t with (t_2, ..., t_r) != 0 is uniform, and the q slices with
  t_2 = ... = t_r = 0 are the maps of Lemma 2. So Phi = log2 q - (q - 1)/q^r, and

      beta_(q,r) <= q * 2^(-(q-1)/q^r).

- (c) r >= 2 and f(u) = N(u_1, u_2), where N(x, y) = x^2 + a x y + b y^2 with t^2 + a t + b
  irreducible over F_q. N(x, y) is the norm of x - y theta from F_(q^2) (theta a root), so it
  vanishes only at 0 and takes each nonzero value q + 1 times. Its polar form
  N(x + y) - N(x) - N(y) is nondegenerate (for even q because a != 0), so every linear function
  <t', u> of (u_1, u_2) equals N(u + c) - N(u) - N(c) for some c, and N(u) + <t', u> = N(u + c) - N(c)
  is a translate of N. So the q^2 slices with t_3 = ... = t_r = 0 all have the law of N, the others
  are uniform, and

      Phi = log2 q - D(q)/q^r,    D(q) = q^2 log2(1 + 1/q) - log2(q + 1).

The square wins for q = 3, 4, 5 (deficit q - 1 against D(3) = 1.735, D(4) = 2.83, D(5) = 3.99),
and the norm form wins for every q >= 7 (D(7) = 6.440 against 6). Both beat KLSS for every q >= 3
and r >= 2: (b) because q - 1 > log2 q, and Theorem 4 of KLSS is weaker still. For q = 2 all
three give at best 2^(3/4) at r = 2, the value KLSS already had, and section 11 shows that no
construction does better.

| q | rank 2: KLSS lower bound | best KLSS upper bound | Theorem 5 | witness |
|---|---|---|---|---|
| 2 | 1.6000 | 1.6818 | 1.6818 (exact, section 11) | f = 0 (no gain) |
| 3 | 2.4545 | 2.6553 | **2.5717** | u_1^2 |
| 4 | 3.3684 | 3.6680 | **3.5125** | u_1^2 |
| 5 | 4.3103 | 4.6883 | **4.4751** | u_1^2 |
| 7 | 6.2364 | 6.7275 | **6.3905** | norm |
| 8 | 7.2113 | 7.7442 | **7.3595** | norm |

For rank 3 over F_3 the three numbers are 2.7931, 2.8804 and **2.8499**.
`python higher_rank.py table` prints these for r = 2, 3, 4.

**Corollary 5 (the second-order term).** For every q and every r >= 2,

    q - q^(2-r) + q^(1-r)  <=  beta_(q,r)  <=  q - q^(2-r) + (1 + ln(q + 1)) q^(1-r).

So beta_(q,r) = q - q^(2-r) + O(q^(1-r) log q), and in particular beta_(q,2) = q - 1 + O((log q)/q).
Before, the best upper bound was q^(1 - q^(-r)) = q - (ln q) q^(1-r) + ..., which does not show
the term -q^(2-r) at all.

*Proof.* Lower: q / (1 + x) >= q (1 - x) with x = (q - 1)/q^r. Upper: by Corollary 4(c),
beta_(q,r) <= q e^(-y) with y = (ln 2) D(q)/q^r = (q^2 ln(1 + 1/q) - ln(q + 1))/q^r, and
q e^(-y) <= q (1 - y + y^2/2). Since ln(1 + 1/q) >= 1/q - 1/(2q^2), q y >= (q - 1/2 - ln(q + 1)) q^(1-r);
since y <= q^(1-r), q y^2/2 <= q^(3-2r)/2 <= q^(1-r)/2. QED

**Proposition 1 (the limit of one-coordinate witnesses).** Every f has
Phi(f) >= log2 q - log2(1 + (q - 1)/q^r), which is the logarithm of the KLSS lower bound.

*Proof.* Two different columns u, v collide in slice t exactly when <t, u - v> = f(v) - f(u), which
holds for exactly q^(r-1) values of t. So the collision probabilities of the q^r slices add up to
1 + q^(r-1) - 1/q, and their average is (1 + (q - 1)/q^r)/q. Each slice has entropy at least minus
the log of its collision probability, and -log2 is convex. QED

So one-coordinate witnesses cannot go below the known lower bound, and Corollary 5 shows they come
within O(q^(1-r) log q) of it. Narrowing the rest of the gap needs blocks, by the next theorem.

**Theorem 6 (exact formula).** Let g_(r,k) be the least value of
(1/q^r) sum over t in F_q^r of H(P(U) + t U) over maps P : F_q^(r x k) -> F_q^k, where U is a
uniform r x k matrix and t a row vector. Then beta_(q,r) = inf over k of 2^(g_(r,k)/k), and
g_(r,1) is the least Phi.

*Proof.* As for Theorem 2. Putting maps side by side gives g_(r,k+l) <= g_(r,k) + g_(r,l). The
construction of Theorem 5 over the alphabet F_q^k (letters are r x k blocks of columns) gives
beta_(q,r) <= 2^(g_(r,k)/k). For k >= r, a rank-r Kakeya set K0 in F_q^k gives a map with every
P(U) + t U in K0: the row space of U lies in some r-dimensional subspace, and P(U) is a point of a
translate of that subspace inside K0. So g_(r,k) <= log2 K_r(k, q), and the infimum is at most
beta_(q,r) by Fekete's lemma. QED

**Proposition 2 (q = 3, r = 2).** The least Phi over all f : F_3^2 -> F_3 is log2 3 - 2/9, attained
by u_1^2. So 2.5717 is the best that one-coordinate witnesses give for rank-2 Kakeya sets over F_3,
and going lower needs blocks (k >= 2 in Theorem 6). Among the f whose nine slices all take all
three values, the norm form is best.

*Proof.* Write Delta_t = log2 3 - H(slice t); we show sum over t of Delta_t <= 2. A slice has
counts (s_0, s_1, s_2) adding up to 9, and by the proof of Proposition 1 its pair count
C_t = sum of C(s_i, 2) satisfies sum over t of (C_t - 9) = 3 * 36 - 81 = 27. A slice t *misses a
value* if f(u) != c_t - <t, u> for all u.

(i) If three slices t_1, t_2, t_3 miss values, then at every u at most two of the three forbidden
values c_i - <t_i, u> differ. Two of them agree on a line of F_3^2, so the three lines of agreement
cover all nine points, are parallel, and the t_i lie on a line t_0 + F_3 v. Then
f(u) + <t_0, u> is the value not forbidden at u, which depends only on <v, u>, and the slices are
those of a one-variable map plus a uniform part, so the sum is at most 2 by section 4. A fourth such
slice is impossible, since a line of F_3^2 has three points.

(ii) If exactly two slices miss values, a change of variables (adding a linear function and a
constant to f, translating u, a linear map) makes them t = (0, 0) and (1, 0), both missing 0. Then
f(u) = u_1 whenever u_1 != 0, and f(0, u_2) = g(u_2) in {1, 2} with g not constant (otherwise a
third slice misses a value). The slices (0, 0) and (1, 0) have counts {5, 4, 0}
(Delta = 0.5939 each), (2, 0) has {6, 2, 1} (Delta = 0.3606), and the six slices with t_2 != 0 have
{4, 3, 2} or {3, 3, 3} (Delta <= 0.0545). The sum is at most 1.8752.

(iii) If at most one slice misses a value: among count patterns with all three values present,
Delta_t / (C_t - 9) is largest for {4, 4, 1} (0.1928/3 = 0.0643), so with no missing value the sum
is at most 27 * 0.0643 = 1.7353, which the norm form attains with nine {4, 4, 1} slices. With one
missing slice the sum is at most Delta + 0.0643 (27 - (C - 9)) over the patterns {5, 4, 0},
{6, 3, 0}, {7, 2, 0}, {8, 1, 0}, {9, 0, 0}, and the largest of these is 1.8793. QED

For q = 2 the same question has the answer 3/4 (eight of the 16 functions are affine and give 3/4,
the other eight give H(1/4) = 0.8113), so for q = r = 2, the case KLSS single out, one-coordinate
witnesses give nothing beyond their 2^(3n/4). By section 11, neither does anything else.

*Checks.* `test_higher_rank.py` builds the fields F_q for q <= 16 and checks: the slice laws of the
norm form; the closed forms of Corollary 4 against direct computation for r = 1, 2 (all ten fields)
and r = 3 (q <= 5); the collision count and the floor of Proposition 1 on the witnesses and on
random f; the translation step of Theorem 5 on random column laws; Theorem 5 with one block on every
plane of F_3^4, F_2^5 and F_4^3 (130, 155 and 21 planes): some translate of the witness gives a
flat whose points have average log2 N at most n Phi(f); Corollary 5 and the comparison with KLSS
for q up to 64 and r = 2, 3, 4; and every number quoted in this section.

*Prior work.* We searched (2026-10-15) for constructions of rank-r Kakeya sets over a fixed field
after KLSS. Dhar, Dvir and Lund (2019) still cite KLSS Theorem 4 as the construction for this
case, and we found nothing better. We could not read K. Cong's 2021 MIT RSI report on Furstenberg
sets over finite fields, which includes constructions. If any of this is known, please open an
issue.

## 11. Kakeya sets of rank r over F_2: the exact growth base (new in 1.5)

In their closing section KLSS write that "even the case q = r = 2 seems non-trivial": they knew no
rank-2 Kakeya set in F_2^n smaller than the O(2^(3n/4)) given by 4-universal sets (sets containing
a translate of every 4-point set), and they asked for lim K_r(n, q)^(1/n) "even for just one
particular pair (q, r) != (2, 1)". For q = 2 the answer is the universal-set bound, for every r.

**Theorem 7.** Let n >= r >= 1. Every Kakeya set K of rank r in F_2^n has

    |K| >= 2^((1 - 2^(-r)) n).

**Corollary 6.** beta_(2,r) = 2^(1 - 2^(-r)) for every r >= 1. More precisely, for all n >= r,

    2^((1 - 2^(-r)) n)  <=  K_r(n, 2)  <  2^((1 - 2^(-r)) n + r + 1),

where the upper bound is KLSS Corollary 11. In particular every rank-2 Kakeya set in F_2^n has
at least 2^(3n/4) points, so the 4-universal sets are optimal up to a factor 8. In Theorem 6,
g_(r,k) = (1 - 2^(-r)) k for q = 2: over F_2, blocks never help.

The proof is one entropy inequality.

**Lemma 5.** Let d_1, ..., d_r be independent and uniform on F_2^n, and let A be any random point
of F_2^n (with any joint law with the d_i). For t in F_2^r put Y_t = A + t_1 d_1 + ... + t_r d_r.
Then

    sum over t in F_2^r of H(Y_t) >= (2^r - 1) n.

*Proof.* Induction on r; for r = 0 the claim is H(A) >= 0. Let r >= 1 and pair each t with
t_1 = 0 with t + e_1. Since Y_(t + e_1) = Y_t + d_1, the pair (Y_t, Y_(t + e_1)) determines and is
determined by (Y_t, d_1), so

    H(Y_t) + H(Y_(t + e_1)) >= H(Y_t, d_1) = n + H(Y_t | d_1).

Adding over the 2^(r-1) pairs, the sum is at least 2^(r-1) n plus the sum over t with t_1 = 0 of
H(Y_t | d_1). Given d_1 = delta, the vectors d_2, ..., d_r are still independent and uniform, and
these Y_t are A + t_2 d_2 + ... + t_r d_r, so by induction that sum is at least (2^(r-1) - 1) n
for every delta. In total the sum is at least (2^r - 1) n. QED

*Proof of Theorem 7.* For each tuple d = (d_1, ..., d_r) the span of the d_i has dimension at most
r <= n, so it lies in an r-dimensional subspace, a translate of which lies in K. Let A = A(d) be a
point with A + span(d_1, ..., d_r) inside K. Then every Y_t lies in K, so H(Y_t) <= log2 |K|, and
Lemma 5 gives 2^r log2 |K| >= (2^r - 1) n. QED

*Proof of Corollary 6.* Theorem 7 and KLSS Corollary 11. For Theorem 6, apply Lemma 5 with n = k,
the d_i the rows of U and A = P(U): this gives g_(r,k) >= (1 - 2^(-r)) k, and P = 0 attains it.
QED

| r | KLSS lower bound 2^(r+1)/(2^r + 1) | beta_(2,r) = 2^(1 - 2^(-r)) |
|---|---|---|
| 1 | 1.3333 | 1.4142 (known: difference bases) |
| 2 | 1.6000 | **1.6818** |
| 3 | 1.7778 | **1.8340** |
| 4 | 1.8824 | **1.9152** |

(`python f2_rank.py table` prints this table.) For r = 1 Theorem 7 is the classical bound
|K| >= 2^(n/2) for difference bases of F_2^n.

**Why counting is not enough.** A 2^r-universal set needs
|K|^(2^r) >= (2^n - 1)(2^n - 2) ... (2^n - 2^r + 1), about 2^((2^r - 1) n), by counting: each of
the C(2^n - 1, 2^r - 1) sets of 2^r points containing 0 has a translate in K, and a 2^r-point
subset of K is a translate of at most 2^r of them. A rank-r
Kakeya set has to contain far fewer configurations, and counting the tuples a, a + w_1, ..., a + w_r
gives only base 2^(r/(r+1)) (1.5874 for r = 2, below the 1.6 of KLSS Theorem 1). Lemma 5 shows
that over F_2 a rank-r Kakeya set must nevertheless be as large as a 2^r-universal set, up to the
factor 2^(r+1).

**Why only q = 2.** Over F_q the same pairing, using one pair on each line in direction d_1 and
keeping the other q - 2 points, gives sum over t of H(Y_t) >= (q^r - (q - 1)^r) n log2 q, so base
q^(1 - (1 - 1/q)^r). For q >= 3 this is weaker than KLSS Theorem 1, because
(q - 1)^(r-1) ln q >= 1. Over F_2 the lines have only two points, and nothing is lost.

**Proposition 3 (small cases).** K_(n-1)(n, 2) = 2^n - 1 for n >= 2, and K_(n-2)(n, 2) = 2^n - 3
for n >= 3.

*Proof.* Write K = F_2^n minus C. K has rank r exactly when, for every r-dimensional subspace W,
C misses a coset of W, that is, the quotient map from F_2^n onto F_2^n / W is not onto on C. For
r = n - 1 the quotient has two points: a set C = {x, y} maps onto it whenever x + y is not in W,
which happens for some hyperplane W, and a single point never does. For r = n - 2 the quotient
F_2^n / W has four points, so a C with at most 3 points is always fine. A C with 4 points,
translated to {0, a, b, c}, maps onto F_2^2 under every linear map with a -> (1, 0), b -> (0, 1),
c -> (1, 1); such a map exists whether a, b, c are independent or c = a + b, and its kernel has
dimension n - 2. QED

So the smallest sets are far above the bound in small dimensions (K_2(4, 2) = 13 against
2^3 = 8): Theorem 7 is about the growth rate.

*Checks.* `test_f2_rank.py` checks: the subspace counts and coset partitions of F_2^n for n <= 5;
the exact values K_r(n, 2) for every n <= 4 by exhaustive search (2, 3, 4, 5, 7, 8, 6, 13, 15 and
16 for (n, r) = (1, 1), (2, 1), (2, 2), (3, 1), (3, 2), (3, 3), (4, 1), (4, 2), (4, 3), (4, 4)),
each above the bound of Theorem 7 and below KLSS Corollary 11; Proposition 3 in F_2^5 for r = 4
and r = 3 (every complement of 1 or 3 points containing 0 is Kakeya, no complement of 2 or 4
points is); Lemma 5 for every deterministic A when (n, r) = (1, 1), (1, 2), (1, 3), (2, 1), and
at the local minima of 128 descents from random starts for (2, 2), (1, 4), (2, 3), (3, 2), and on
random laws of A; that A = 0 attains it; that the witnesses of the smallest sets put every Y_t in
K; and every number quoted in this section. The case (n, r) = (2, 2) of Lemma 5 is the block
question of Theorem 6 for q = r = 2 and k = 2: no map P on 2 x 2 matrices over F_2 has slice
entropies adding up to less than 6.

*Prior work.* We searched (2026-10-15) for lower bounds on rank-r Kakeya sets over F_2 after KLSS:
the papers citing it, Ellenberg-Oberlin-Tao, Dhar-Dvir-Lund (whose entropy formulation uses
min-entropy and large q), and the universal-set paper of Alon, Bukh and Sudakov. KLSS prove their
Theorem 1 with the polynomial method, and we found no better lower bound for q = 2 and r >= 2.
If Theorem 7 is known, please open an issue and we will cite it.

## 12. What is and is not claimed

- Proved here: Theorem 1 for every prime power q, Lemma 2, the limit of one-coordinate witnesses
  (section 4), the deterministic q = 3 version, the entropy formula (Theorem 2 and its corollaries),
  Theorem 3 with Lemma 4, Theorem 4 and Corollary 3, and for higher rank Theorems 5, 6 and 7,
  Lemma 5, Corollaries 4, 5 and 6 and Propositions 1, 2 and 3.
- Computed (exhaustive, with the checks above): max S = 36 over all maps on F_3^2, so h_2 = 2 h_1
  for q = 3; the values K_r(n, 2) for n <= 4.
- New, as far as we could find: every bound in the table for q >= 4, the explicit construction at
  q = 3, Theorems 2, 3 and 4, Lemma 4, the value h_2 = 2 h_1 for q = 3, every rank-r bound in
  section 10 for q >= 3 and r >= 2, including the second-order term of Corollary 5, and the exact
  value beta_(2,r) = 2^(1 - 2^(-r)) for every r >= 2 (Theorem 7 and Corollary 6). The bound for
  q = 3 in section 1 is not new (KLSS proved it with a random construction), and neither is the
  case r = 1 of Theorem 7 or the upper bound of Corollary 6 (KLSS Corollary 11).
- Not claimed: any value of beta_q for q >= 3 or of beta_(q,r) for q >= 3, any improvement below
  1.8899 for q = 3, or that h_k = k h_1 for k >= 3. The gap between q * 2^(-(q-1)/q) and
  q^2/(2q - 1) is open for every q >= 3.
- The O(n^(2/3) log n) error term means the bounds of sections 3 to 10 beat earlier constructions
  only in large dimension. They are about the exponential growth rate, not about small cases.
- `paper/kakeya-small-fields.tex` covers Theorems 1 to 3 in their version 1.1 form. Sections 7 to
  10 of this README are newer than that preprint. `paper/kakeya-rank-r-f2.tex` is a short
  self-contained note with section 11.

## 13. The code and the tests

`kakeya_entropy.py` is pure Python with no dependencies. It implements F_q for q in {2, 3, 4, 5, 7,
8, 9, 11, 13, 16, 25, 27}, the maps g_t, the entropy sums, the block construction, the deterministic
q = 3 witness, the bound formulas, h(P) and S(P), witness maps of Kakeya sets, a local search, and
the section 7 quantities. `search_h2.py` holds a numpy exhaustive search and an annealing search.
`exact_h2.py` is the pure-Python branch and bound of section 9 (`python exact_h2.py --q 3 --k 2`).
`higher_rank.py` (pure Python) holds the section 10 witnesses, bounds and checks
(`python higher_rank.py table`). `f2_rank.py` (pure Python) holds section 11: subspaces and
Kakeya sets of F_2^n, the exhaustive search for small n (`python f2_rank.py small`), the slice
entropies of Lemma 5 and a local search for base points that would break it.
`python -m unittest -v` checks:

- the field tables, and the fibre structure of x^2 + t x in all twelve fields;
- Lemma 2 at the uniform distribution (exactly) and against random and point distributions, and its
  translation invariance;
- the limit of section 4 for all q^q functions f when q <= 5, and h_1 = c_q by exhausting all maps;
- Lemmas 1 and 2 together for every block u, up to F_3^5, F_4^4, F_5^3 and F_9^2;
- that the sets K built with the smallest threshold for which every direction has a line are
  Kakeya, by brute force over all directions, for q = 3, 4, 5 and 8 in dimensions up to 6, and
  that Lemma 3's bound holds for every direction there;
- that the deterministic q = 3 lines lie in K3 for every direction up to F_3^6 and for random
  directions up to F_3^90, that K3 is Kakeya (brute force) and within its size bound;
- h(P) = k log2 q - S(P)/q^(k+1); h of the coordinatewise squares is k c_q for eight (q, k);
  h_2 = 1 for q = 2 over all 256 maps; h(P) is unchanged by P -> P + c and P -> P + lam x;
  witness maps of Kakeya sets have h(P) <= log2 |K|; every map tested respects Corollary 2;
- Theorem 3(a) for random and all deterministic couplings; Lemma 4 and Theorem 3(b) (section 7);
- Theorem 4 and Corollary 3 (section 8);
- the exhaustive search of section 9 and its cross-checks;
- the higher-rank results of section 10 (listed there);
- the F_2 results of section 11 (listed there);
- every number quoted in this README.

## 14. Sources

- S. Kopparty, V. F. Lev, S. Saraf, M. Sudan, "Kakeya-type sets in finite vector spaces",
  J. Algebraic Combin. 34 (2011) 337-355; arXiv 1003.3736 (Theorems 1, 4, 6, 7, 8, 10,
  Corollary 11; section 6).
- G. Kyureghyan, P. Muller, Q. Wang, "On the size of Kakeya sets in finite vector spaces",
  Electron. J. Combin. 20(3) (2013) #P36; arXiv 1302.5591.
- B. Bukh, T.-W. Chao, "Sharp density bounds on the finite field Kakeya problem", Discrete
  Analysis 2021:26; arXiv 2108.00074.
- Z. Dvir, S. Kopparty, S. Saraf, M. Sudan, "Extensions to the method of multiplicities, with
  applications to Kakeya sets and mergers", FOCS 2009; S. Saraf, M. Sudan, arXiv 0808.2499.
- J. Ellenberg, R. Oberlin, T. Tao, "The Kakeya set and maximal conjectures for algebraic varieties
  over finite fields", Mathematika 56 (2010) (Kakeya sets of rank r).
- M. Dhar, Z. Dvir, B. Lund, "Simple proofs for Furstenberg sets over finite fields",
  arXiv 1909.03180 (2019).
- N. Alon, B. Bukh, B. Sudakov, "Discrete Kakeya-type problems and small bases", Israel J. Math.
  174 (2009) 285-301 (universal sets).
- T. Banakh, V. Gavrylkiv, on difference bases of finite groups, 2019 (the case q = 2).
- B. Georgiev, J. Gomez-Serrano, T. Tao, A. Z. Wagner, "Mathematical exploration and discovery at
  scale", arXiv 2511.02864 (2025).
- T. Tao, "New Nikodym set constructions over finite fields", arXiv 2511.07721 (2025).
- I. Csiszar, "The method of types", IEEE Trans. Inform. Theory 44 (1998) 2505-2523 (class sizes).
- MV2 of Munim, Inc., kakeya-conjecture (exposition, K(3, 3) = 13, the base-1.9626 construction),
  https://github.com/munimtechnologies/kakeya-conjecture

## Licence

Text CC BY 4.0; code Apache-2.0 (see LICENSE). By MV2 of Munim, Inc.; researched and written with
AI agents working in his name.
