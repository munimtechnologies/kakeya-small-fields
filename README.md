# Smaller Kakeya sets over small finite fields

**New upper bound: lim K(n, q)^(1/n) <= q * 2^(-(q-1)/q) for every finite field F_q.**
**New in 1.1: an exact entropy formula for that limit, and a proof that sets symmetric under
permuting coordinates cannot beat the bound.**

By MV2 of Munim, Inc. Version 1.1, 2026-10-15. This note and its code were researched and written
with AI agents working in MV2's name; every claim below is proved here, and the finite cases are
checked by the tests in `test_kakeya_entropy.py` and `test_search_h2.py`. Text CC BY 4.0, code
Apache-2.0.

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

Version 1.1 shows that this averaging loses nothing (section 6). For a map P : F_q^k -> F_q^k let
h(P) = (1/q) sum over t of H(P(X) + t X), with X uniform on F_q^k, and let h_k be the least h(P).
Then

    beta_q = inf over k of 2^(h_k / k)        (Theorem 2),

and h_1 = log2 q - (q-1)/q, which is the bound above. So the bound is the true value of beta_q
exactly when h_k = k h_1 for every k. A single map P on F_q^k with h(P) < k h_1, a finite object
that a computer can check, would give an explicit Kakeya construction beating it. Section 7 shows
that no Kakeya set invariant under permuting coordinates beats the bound, and that for q = 3 such
sets cannot even reach it. Section 8 states the smallest open finite case (maps on F_3^2).

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
Section 6 shows exactly what such witnesses must do, and section 7 that the set cannot be symmetric
under all permutations of the coordinates.

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

## 7. Sets symmetric under permuting coordinates (new in 1.1)

Most explicit constructions are unions of composition classes: a point's membership depends only
on how often each symbol occurs. Theorem 1's set is not: it is symmetric only within blocks.

**Theorem 3.** (a) If K in F_q^n is a Kakeya set that is invariant under all permutations of the
coordinates and q divides n, then |K| >= (q * 2^(-(q-1)/q))^n / (n + 1)^q.

(b) For q = 3 there is a delta > 0 such that every permutation-invariant Kakeya set in F_3^n with n
even has |K| >= 2^((c_3 + delta) n) / (n + 1)^3, where 2^(c_3) = 1.8899. The permutation-invariant
set of points that use at most two of the three symbols is a Kakeya set with 3 * 2^n - 3 points.

So permutation-invariant Kakeya sets never beat q * 2^(-(q-1)/q), and over F_3 their best base lies
in the interval (1.8899, 2]. Theorem 1 needs its block structure. (Part (a) is far from sharp for
q = 2: a union of Hamming-weight levels needs about 2^(0.81 n) points to contain every difference,
while beta_2 = sqrt 2.)

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

*Proof of (b).* Take u with n/2 zeros and n/2 ones. If the symbols of a are distributed as k0 where
u is 0 and as k1 where u is 1, then point t of the line has symbol distribution
M_t(z) = (k0(z) + k1(z - t)) / 2. We show max over t of H(M_t) > h(2/3) = c_3 for every k0, k1
(h is the binary entropy). The minimum over k0, k1 is attained, so it equals c_3 + delta with
delta > 0, and the class-size bound finishes as in (a).

Suppose H(M_t) <= h(2/3) for t = 0, 1, 2. A distribution on three points whose largest mass p is
below 2/3 has entropy above h(2/3): if p < 1/2 its entropy is at least log2(1/p) > 1, and if
1/2 <= p < 2/3 it is at least h(p) > h(2/3). So for each t there is a symbol z_t with
k0(z_t) + k1(z_t - t) >= 4/3, and A + B >= 4 for A = sum_t k0(z_t), B = sum_t k1(z_t - t).
If z_s = z_t for s != t then z_s - s != z_t - t. If all three z_t are equal, A <= 3 and the
z_t - t are distinct, so B = 1. If exactly two are equal, A <= 2 and B <= 2. If all are distinct,
A = 1 and B <= 3. So A + B = 4: every M_t has largest mass exactly 2/3, and H(M_t) <= h(2/3) then
puts the remaining 1/3 on one symbol. In the first case k0 is a point mass and k1 is uniform, so
M_t = (2/3, 1/6, 1/6); in the third case k1 is a point mass and k0 uniform, with the same M_t; in
the second both are point masses and every mass of every M_t is 0, 1/2 or 1. Each case contradicts
the shape (2/3, 1/3, 0). QED

The two-symbol set is Kakeya because g_t(u) = u^2 + t u uses at most two symbols (g_t has a fibre
of size 2 on F_3), and it has 3 (2^n - 2) + 3 points. We conjecture that the minimum in (b) is
exactly 1 (point masses attain 1, and we checked by hand that nothing below 1 occurs when k0 is a
point mass), which would make the best base for permutation-invariant sets over F_3 exactly 2.
`python kakeya_entropy.py entropy` prints the minimum over a grid.

## 8. The smallest open case: maps on F_3^2

By Corollary 1, beta_3 < 1.8899 would follow from one map P : F_3^2 -> F_3^2 with S(P) > 36,
that is, from nine lines in nine non-vertical directions of F_3^3 whose three horizontal slices are
more concentrated, in total entropy, than the coordinatewise squares (which have S = 36, each
slice with fibre sizes 4, 2, 2, 1). Corollary 2 caps S at 39.80. The same windows for k = 2:

| q | S of the squares = threshold | ceiling from the lower bound |
|---|---|---|
| 3 | 36 | 39.80 |
| 4 | 96 | 103.34 |
| 5 | 200 | 212.00 |

There are 9^9 maps on F_3^2, and since P -> P + c does not change S, the 9^8 = 43,046,721 maps with
P(0) = 0 cover them all. `search_h2.py exhaustive --q 3 --k 2` checks every one of them with numpy
in a few minutes, and `search_h2.py anneal` runs simulated annealing for larger q and k. This
version does not include their results; we will add them, positive or negative.

## 9. What is and is not claimed

- Proved here: Theorem 1 for every prime power q, Lemma 2, the limit of one-coordinate witnesses
  (section 4), the deterministic q = 3 version, the entropy formula (Theorem 2 and its corollaries)
  and Theorem 3.
- New, as far as we could find: every bound in the table for q >= 4, the explicit construction at
  q = 3, Theorem 2 and Theorem 3. The bound for q = 3 is not new (KLSS proved it with a random
  construction).
- Not claimed: any value of beta_q, any improvement below 1.8899 for q = 3, or that h_k = k h_1.
  The gap between q * 2^(-(q-1)/q) and q^2/(2q - 1) is open for every q >= 3.
- The O(n^(2/3) log n) error term means the bound beats earlier constructions only in large
  dimension. The bound is about the exponential growth rate, not about small cases. The delta of
  Theorem 3(b) comes from a compactness argument and is not explicit.

## 10. The code and the tests

`kakeya_entropy.py` is pure Python with no dependencies. It implements F_q for q in {2, 3, 4, 5, 7,
8, 9, 11, 13, 16, 25, 27}, the maps g_t, the entropy sums, the block construction, the deterministic
q = 3 witness, the bound formulas, h(P) and S(P), witness maps of Kakeya sets, a local search, and
the section 7 quantities. `search_h2.py` holds the exhaustive (numpy) and annealing searches of
section 8. `paper/kakeya-small-fields.tex` is a LaTeX preprint of Theorems 1-3 with the same
proofs. `python -m unittest -v` checks:

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
- Theorem 3(a) for random and all deterministic couplings, 3(b) on a grid, and the Kakeya property
  and size of the two-symbol set up to F_3^4;
- the exhaustive search against brute force and known values (when numpy is installed);
- every number quoted in this README.

## 11. Sources

- S. Kopparty, V. F. Lev, S. Saraf, M. Sudan, "Kakeya-type sets in finite vector spaces",
  J. Algebraic Combin. 34 (2011) 337-355; arXiv 1003.3736 (Theorems 1, 6, 7, 8).
- G. Kyureghyan, P. Muller, Q. Wang, "On the size of Kakeya sets in finite vector spaces",
  Electron. J. Combin. 20(3) (2013) #P36; arXiv 1302.5591.
- B. Bukh, T.-W. Chao, "Sharp density bounds on the finite field Kakeya problem", Discrete
  Analysis 2021:26; arXiv 2108.00074.
- Z. Dvir, S. Kopparty, S. Saraf, M. Sudan, "Extensions to the method of multiplicities, with
  applications to Kakeya sets and mergers", FOCS 2009; S. Saraf, M. Sudan, arXiv 0808.2499.
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
