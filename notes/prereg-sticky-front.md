# Pre-registration: are sticky Kakeya sets over F_3 forced up to base 2? (job sticky-front-v1)

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19. Made with AI agents working in MV2's name.
**No human mathematician has checked this note.** Text CC BY 4.0, code Apache-2.0.
Code: `sticky_front.py`, tests `test_sticky_front.py`. Builds on a182 (Corollary 71.3).
Written before the job has run. Nothing below is a result of the job.

## The question

a182 defined *sticky* Kakeya sets in F_3^n: lines P(d) + F_3 d with coordinate j of P(d) depending
only on d_1..d_j, in some basis. It proved |K| >= (3^n - 1)^(1/R0), base (27/4)^(1/3) = 1.889882,
the same base as the KLSS upper bound for all Kakeya sets. The best sticky construction we know,
{0,1}^n u {0,2}^n, has base 2.

> **Conjecture S.** Sticky Kakeya sets in F_3^n have size 2^(n - o(n)).

If true, then for large n **no smallest Kakeya set over F_3 is sticky**, because KLSS-type sets of
base 1.889882 exist. That would contrast with the Euclidean problem, where Wang and Zahl (2025)
reduce the Kakeya conjecture in R^3 to sticky sets. If false, then sticky sets reach the KLSS
base, and the exact growth constant of sticky Kakeya sets over F_3 is (27/4)^(1/3).

## Proved reductions (Lemmas 149-152)

A sticky configuration is a ternary tree of depth n. The node at prefix a carries the map
g_a(x) = P_j(a, x) of F_3. By a182 every map of F_3 is **affine** with a constant slice s, or a
**triangle**. A triangle merges one pair of children in each slice t and isolates the third, and
t -> isolated child is a bijection. All 6 bijections occur, since i(t) = ±(t + s).

**Lemma 149 (selection bound).** Define vectors L(a) in Z^3 by L = (1,1,1) at the leaves and
- affine with constant slice s: L_s(a) = max_x L_s(ax), and L_t(a) = sum_x L_t(ax) for t != s;
- triangle: L_t(a) = L_t(a i(t)) + max_{x != i(t)} L_t(ax).

Then |Im Y_t| >= L_t(root) for each slice t. Hence every sticky Kakeya set has
|K| >= max_t L_t(root) - 1. (The -1 is the point chosen for the zero direction.)
*Proof.* Group the slice-t image of the subtree at a by the value of coordinate j:
|Im_t(a)| = sum_c |U_{x: g_a(x)+tx=c} Im_t(ax)| >= sum_c max_x |Im_t(ax)|. Then induct. ∎

Let f(h) be the minimum of max_t L_t over all trees of height h. Triangles everywhere give 2^h, so
f(h) <= 2^h. Conjecture S follows from **Conjecture S2: f(h) >= 2^(h - o(h)).**

**Lemma 150.** For t != t', L_t L_t' >= 3^h, and L_0 L_1 L_2 >= (27/4)^h.
*Proof.* For the first claim, induct. At an affine node, max·sum and sum·sum are both
>= sum_x L_t(x) L_t'(x). At a triangle node, expand (L_t(z) + m)(L_t'(z') + m'), where z, z' are
the children isolated in slices t and t', and m, m' are the pair maxima. The cross terms dominate
L_t(z)L_t'(z), L_t(z')L_t'(z') and L_t(y)L_t'(y). For the second claim, use the Gibbs variational
formula: log L_t >= sum_j E H(Y_{t,j} | D_<j) under the uniform law. Each node then contributes
log(27/4) (triangle) or 2 log 3 (affine) to the sum over t, as in Lemma 148. ∎

**Lemma 151.** The height-1 vectors are (2,2,2) and the permutations of (1,3,3). f(1) = 2 and
f(2) = 4. (3,3,9) is a minimal height-2 vector: two slices of size 3 force the third to be 9.

**Lemma 152 (affine nodes cannot beat 2 by much).** Put A(L) = (min L + max L)/2 and
G(L) = (L_0 L_1 L_2)^(1/3). Suppose every child of an affine node has G >= g. Then the parent has
G >= 9^(1/3) g and A >= beta* g, where beta* = (243/32)^(1/3) = 1.96556.
*Proof.* Let c^ be the coordinatewise geometric mean of the children. The parent is >= (c^_s, 3c^_t,
3c^_t') coordinatewise, and min+max is monotone. Over (a, b, d) with abd >= g^3, the three
orderings give min+max >= a + 3a^(-1/2) g^(3/2) or a + 9g^3/a^2. Both are minimised at the value
(9/2)(2/3)^(1/3) g. ∎

**Remark (why a one-step potential is not enough).** min(A, G) fails at triangle nodes. Take the
three children (1, 2, 1/2), (2, 1, 1/2) and (2, 2, 1/4). Each has A >= 1 and G = 1. Isolate child t
in slice t; the parent is (3, 3, 3/4), with A = 1.875 and G = (27/4)^(1/3). So this potential cannot
certify any base above 1.875. Whether such shapes can really occur at the right scale is exactly
what the fronts below show. At heights 1 and 2 every vector satisfies min + max >= 2^(h+1), and the
"Latin" triangle over (a, b, b) with a + b = 2^(h+1) gives exactly 2^(h+1).

## The job (sticky-front-v1)

`sticky_front.py --hmax 9` computes the exact Pareto fronts of achievable L-vectors for
h = 1..9, pruned to max <= 2^9. This is exact for f(h) when h <= 9, because every parent
coordinate is >= the same coordinate of every child. It first checks that the numpy step equals
the pure-Python step for h <= 3. For each h it reports f(h); min(min + max), to test Conjecture M:
min + max >= 2^(h+1); the smallest product among the pruned vectors; and the proved
Lemma 150 checks. A Lemma 150 failure would mean a bug.

**Reading rules, fixed now.**
- **S-SUPPORT:** f(h) = 2^h for every computed h. This is evidence for S2, not a proof. The next
  step is a proof attempt guided by the fronts, for example an invariant fitted to them.
- **S-BREAK:** f(h) < 2^h for some h. The job prints a witness and its derivation. The next step
  is to check whether the witness is realised by an actual sticky set (nested images). If it is,
  count |K| exactly for that n. That would be the first sticky Kakeya set below 2^n we know of.
- **M:** we report whether min + max >= 2^(h+1) at every height. A failure of M alone decides
  nothing about S.
- If the job stops early (front too large or out of time), we report the heights reached and
  nothing more.

## Prior art

We know of no finite-field notion of sticky Kakeya sets before a182, and no study of this
selection game. Searches covered Dvir; Dvir-Kopparty-Saraf-Sudan; Kopparty-Lev-Saraf-Sudan (J.
Algebr. Comb. 34, 2011); Bukh-Chao; and Wang-Zahl. Pointers are welcome.
