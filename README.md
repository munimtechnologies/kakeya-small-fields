# Smaller Kakeya sets over small finite fields

**New upper bound: lim K(n, q)^(1/n) <= q * 2^(-(q-1)/q) for every finite field F_q.**

By MV2 of Munim, Inc. Version 1.0, 2026-10-14. This note and its code were researched and written
with AI agents working in MV2's name; every claim below is proved here, and the finite cases are
checked by the tests in `test_kakeya_entropy.py`. Text CC BY 4.0, code Apache-2.0.

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

We searched the web and arXiv for a better bound with q fixed and n growing (searches of
2026-10-14, including later work on these constructions) and found none. The 2025 AlphaEvolve Kakeya
results (Georgiev, Gomez-Serrano, Tao, Wagner) are for fixed dimension 3 to 5 and large q. If an
earlier proof of these bounds exists, we would like to cite it; please open an issue.

## 3. The construction

Fix q and integers m, r >= 1, and let n = r m. Cut x in F_q^n into r blocks x^(1), ..., x^(r) of
length m. For y in F_q^m let N(y) be the number of vectors with the same symbol counts as y (a
multinomial coefficient), and put

    w(x) = log2 N(x^(1)) + ... + log2 N(x^(r)),
    K = { x in F_q^n : w(x) <= T },    T = r m c_q + m log2(q) sqrt(r ln q),
    c_q = log2 q - (q - 1)/q.

Membership is decided by counting symbols, so K is explicit.

**Theorem.** K is a Kakeya set, and
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

This proves the Theorem. Only the *existence* of the shifts uses probability; the set K itself is
explicit, and good shifts can be found deterministically (by the method of conditional
expectations, or by the exact rule below when q = 3).

**Why it works.** KLSS's Theorem 6 uses the same lines (for odd q, f(x) = x^2) but must contain every
point of every such line in a single symmetric set, so it pays for the largest image
|{f(x) + t x}|. Here the q points of a line take turns being cheap on different blocks, so each
point pays the average over t, and the composition classes make it the entropy rather than the
support size. At the uniform distribution the average is log2 q - (q - 1)/q, against
log2 ((q + 1)/2) for Theorem 6 and log2 q - 2/q for Theorem 8. These coincide only at q = 3.

## 4. This is the limit of the method

For *any* function f : F_q -> F_q and the uniform distribution,
sum over t of H(f(x) + t x) >= q log2 q - (q - 1). Two points x != y collide under f(x) + t x for
exactly one t, so the C(q, 2) pairs are shared out among the q maps. A fibre of size s lowers the
entropy by (s log2 s)/q and uses C(s, 2) pairs, and s log2 s <= s(s - 1) = 2 C(s, 2) with equality
only for s <= 2. So the total reduction is at most q - 1, and it is reached exactly when all fibres
have size at most 2, as for f = x^2. (The tests check this for every f when q <= 5.) Going below
q * 2^(-(q-1)/q) therefore needs witnesses that are not of the form "one function per coordinate",
or sets that are not unions of composition classes.

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

## 6. What is and is not claimed

- Proved here: the Theorem for every prime power q, Lemma 2, the limit of the method (section 4),
  and the deterministic q = 3 version.
- New, as far as we could find: every bound in the table for q >= 4, and the explicit construction
  at q = 3. The bound for q = 3 is not new (KLSS proved it with a random construction).
- Not claimed: any value of beta_q, or any improvement below 1.8899 for q = 3. The gap between
  q * 2^(-(q-1)/q) and q^2/(2q - 1) is open for every q >= 3.
- The O(n^(2/3) log n) error term means the bound beats earlier constructions only in large
  dimension. The bound is about the exponential growth rate, not about small cases.

## 7. The code and the tests

`kakeya_entropy.py` is pure Python with no dependencies. It implements F_q for q in {2, 3, 4, 5, 7,
8, 9, 11, 13, 16, 25, 27}, the maps g_t, the entropy sums, the block construction, the deterministic
q = 3 witness and the bound formulas. `python -m unittest -v test_kakeya_entropy` checks:

- the field tables, and the fibre structure of x^2 + t x in all twelve fields;
- Lemma 2 at the uniform distribution (exactly) and against random and point distributions, and its
  translation invariance;
- the method's limit (section 4) for all q^q functions f when q <= 5;
- Lemmas 1 and 2 together for every block u, up to F_3^5, F_4^4, F_5^3 and F_9^2;
- that the sets K built with the smallest threshold for which every direction has a line are
  Kakeya, by brute force over all directions, for q = 3, 4, 5 and 8 in dimensions up to 6, and
  that Lemma 3's bound holds for every direction there;
- that the deterministic q = 3 lines lie in K3 for every direction up to F_3^6 and for random
  directions up to F_3^90, that K3 is Kakeya (brute force) and within its size bound;
- every number quoted in this README.

## 8. Sources

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
- MV2 of Munim, Inc., kakeya-conjecture (exposition, K(3, 3) = 13, the base-1.9626 construction),
  https://github.com/munimtechnologies/kakeya-conjecture

## Licence

Text CC BY 4.0; code Apache-2.0 (see LICENSE). By MV2 of Munim, Inc.; researched and written with
AI agents working in his name.
