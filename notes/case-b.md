# Case B of Question R: its structure, and an exact search in a normal form

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10, next to
[tight-cases.md](tight-cases.md), [question-r.md](question-r.md) and [sat-search.md](sat-search.md).
Numbering continues from tight-cases.md (Lemma 34, Lemma 35, Proposition 27, Corollary 19). This is
partial progress: it settles no new case of Corollary 17. It describes what a Case B element must
look like, and it sets up an exact search that decides Case B directly. It was researched and
written with AI agents working in MV2's name. The proofs are by hand; `cube_groups/case_b.py`
checks Lemma 34 exhaustively and the normal form of Lemma 35 on examples, and its unit tests gated
this commit. No human mathematician has checked the proofs. Text CC BY 4.0, code Apache-2.0.

## What changes

- **Proposition 27** collects what Case B forces. The values of beta on U+ lie in ker A_u n Im A_u.
  If beta vanishes on U+ (always so when U+ has dimension 2), then every element of U+ kills
  ker A_u, and ker A_u n Im A_u has dimension at least k - 1. For k = 3, the only other shapes are
  two explicit ones.
- **Corollary 19.** At t = 6 and rank 3, every Case B element has Im A_u n ker A_u != 0. At t = 7
  and rank 3, a Case B element on whose U+ beta vanishes has A_u^2 = 0.
- **Lemma 35** puts any Case B element in a normal form that fixes sigma(u), all of beta(u, .) and k
  columns of A_u. `cube_groups/case_b.py` turns it into an exact SAT search. Its UNSAT answer for
  (t, k) = (6, 3) would give A(6) <= 7, and for (7, 4) it would give A(7) <= 9, which settles
  Z_4^10 x Z_2^2 (Corollary 18).
- **The search ran** (job m11-caseb-v1, 2026-10-17): every pre-registered prediction held, but the
  three open instances, (6, 3), (7, 4) and (5, 2), reached their time limits undecided. See
  "Results" below. A(6) <= 7 and A(7) <= 9 are still open.

## Setting

As in [tight-cases.md](tight-cases.md): X = F_2^t, a quadratic map sigma : V -> X with polar form
beta, and a linear map h -> A_h from V to End(X) with

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Replacing h by h_1 + h_2 gives the polarised form (proof of Lemma 31)

    A_(h') beta(h_1, h_2) = A_(h_1) beta(h_2, h') + A_(h_2) beta(h_1, h').   (Q)

Throughout, (sigma, alpha) is anisotropic with dim V = t + k - 1, and u has rank rho = t - k with
1 <= rho <= t - 2. We assume A(s) = s for every s <= k. That is one more than Proposition 26 needs,
and it holds for k <= 4 (Theorem 26). Put x0 = sigma(u), phi = beta(u, .), X_1 = ker A_u (dimension
k), R = Im A_u (dimension rho), pi : X -> X/R, and d = dim(X_1 n R). In **Case B**, P = phi(V) is a
hyperplane that does not contain x0, and N = U+ = ker phi has dimension k. Proposition 26(e) says
that for n in N, A_n x0 = 0, sigma(n) lies in X_1, Im A_n lies in R, and sigma(N) spans X_1. Put
Y = P n X_1, of dimension k - 1 (x0 is in X_1 but not in P), and W = phi^(-1)(Y), of dimension
2k - 1, which contains N. We use the identities

    A_h x0 = (I + A_u) phi(h),     A_u sigma(h) = (I + A_h) phi(h)      for all h,     (1)

which are (*) with (h, h') -> (u, h) and h' -> u (proof of Lemma 30).

## Lemma 34 (systems with dim V = dim X = 2)

**Lemma 34.** Every anisotropic system with dim V = dim X = 2 has one of two types:
(i) beta = 0 and alpha = 0 (so sigma is a linear bijection);
(ii) in a suitable basis v_1, v_2 of V, sigma(v_1) = sigma(v_2) = a, delta = beta(v_1, v_2) is not in
    span(a), and A_(v_1) and A_(v_2) both kill a and fix delta.
In fixed bases there are 24 such systems, 6 of type (i) and 18 of type (ii).

*Proof.* With s_i = sigma(e_i) and delta = beta(e_1, e_2), (*) says (equations (L) of
sat-search.md; there is no (Q) for dim V = 2)

    A_1 s_1 = 0,   A_2 s_2 = 0,   A_2 s_1 = (I + A_1) delta,   A_1 s_2 = (I + A_2) delta,

and anisotropy says s_1, s_2 and s_1 + s_2 + delta are not 0. If s_1 and s_2 are independent, write
delta = c_1 s_1 + c_2 s_2. For c_1 = c_2 = 1, sigma(e_1 + e_2) = 0. For c_1 = c_2 = 0, delta = 0 and
both A_i vanish on s_1 and s_2: type (i). For delta = s_2, A_1 s_2 = (I + A_2) s_2 = s_2 and
A_2 s_1 = (I + A_1) s_2 = 0, so A_2 = 0 and A_1 kills s_1 and fixes s_2; in the basis (e_1, e_1 + e_2),
sigma takes the value s_1 twice and beta(e_1, e_1 + e_2) = s_2: type (ii). delta = s_1 is symmetric.
If s_1 = s_2 = a, then sigma(e_1 + e_2) = delta != 0, and delta = a would give
0 = A_2 s_2 = A_2 s_1 = (I + A_1) a = a. So delta is not in span(a), and the equations say that A_1
and A_2 kill a and fix delta: type (ii). In each case alpha is determined, which gives
6 + 6 x 2 + 3 x 2 = 24 systems. QED

## Proposition 27 (the structure of Case B)

**Proposition 27.** In the setting above, let u be in Case B.

(a) beta(N, N) lies in X_1 n R.

(b) pi A_h depends only on p = phi(h). Writing B(p) for it, B(p) p' = B(p') p, B(p) x0 = pi(p) and
    B(p)(p + x0) = 0 for all p, p' in P.

(c) Suppose beta vanishes on N x N. This always holds when k = 2. Then:
    (c1) sigma maps N linearly and bijectively onto X_1, and A_n kills X_1 for every n in N;
    (c2) for every h in W, beta(h, N) lies in X_1, A_h maps X_1 into itself, and
         A_u sigma(h) = (I + A_h) phi(h) lies in X_1 n R;
    (c3) sigma(h) is not in X_1 for h in W outside N;
    (c4) d = dim(X_1 n R) >= k - 1. Hence rho >= k - 1, and if t = 2k - 1, then R lies in X_1, that
         is, A_u^2 = 0.

(d) Let k = 3 and suppose beta does not vanish on N x N. Then N has a basis u, n_1, n_2 with one of:
    (d1) a = sigma(n_1), b = sigma(n_2) and x0 are independent, beta(n_1, n_2) = x0 (so x0 is in R),
         A_(n_1) kills x0 and a and sends b to x0, and A_(n_2) kills x0 and b and sends a to x0;
    (d2) sigma(n_1) = a, sigma(n_2) = delta and beta(n_1, n_2) = delta, where x0, a, delta is a basis of
         X_1 (so delta is in R), A_(n_1) kills x0 and a and fixes delta, and A_(n_2) kills X_1.

*Proof.* (a) For n, n' in N, beta(n, n') = sigma(n + n') + sigma(n) + sigma(n') lies in X_1. In (*)
with h = n and h' = n', A_(n') sigma(n) = beta(n, n') + A_n beta(n, n'), and both A-terms lie in R.

(b) For n in N, A_(h + n) = A_h + A_n and Im A_n lies in R, so pi A_h depends only on phi(h). (Q) with
h_1 = u, h_2 = h gives A_(h') phi(h) = A_u beta(h, h') + A_h phi(h'), which modulo R is
B(p') p = B(p) p'. Modulo R, (1) reads B(p) x0 = pi(p) and pi(p) = B(p) p. Adding gives
B(p)(p + x0) = 0.

(c1) beta = 0 on N makes sigma additive on N, so linear; it is one-to-one (anisotropic), and
dim N = k = dim X_1, so sigma(N) = X_1. In (*) with h = n and h' = n', A_(n') sigma(n) =
(I + A_n) beta(n, n') = 0, so every A_(n') kills X_1. When k = 2, N = span(u, v) and
beta(u, v) = phi(v) = 0.

(c2) Let h be in W, y = phi(h) in Y, and n in N. (Q) with h_1 = u, h_2 = n and h' = h gives
0 = A_h beta(u, n) = A_u beta(n, h) + A_n y, and A_n y = 0 by (c1), as y is in X_1. So beta(n, h)
lies in X_1. In (*) with h -> n and h' -> h, A_h sigma(n) = (I + A_n) beta(n, h) = beta(n, h), which
lies in X_1; as sigma(N) = X_1, A_h maps X_1 into itself. Then A_u sigma(h) = y + A_h y (by (1)) lies
in X_1, and it lies in R.

(c3) If sigma(h) were in X_1 for some h in W outside N, then on U' = N + span(h), of dimension k + 1,
sigma(n + h) = sigma(n) + sigma(h) + beta(n, h) would lie in X_1 by (c1) and (c2). By Lemma 26(a),
U' would carry an anisotropic system with values in X_1, against A(k) = k.

(c4) Let X' = span sigma(W). It contains sigma(N) = X_1, and by (c2) it lies in
X_2 = {x : A_u x in X_1}, which has dimension k + d (A_u maps X_2 onto X_1 n R with kernel X_1). By
Lemma 26(a), W carries a system with values in X', with maps A'_h = (A_h restricted to X',
projected onto X'). By (c1) and (c2), every A'_h maps X_1 into itself. X_1 != X', since otherwise
sigma(W) would lie in X_1, against (c3) (W != N as k >= 2). Divide by X_1 (Lemma 27(a)): this gives
a system on W with values in X'/X_1, of dimension at most d. In it, sigma vanishes on N, and so do
the maps of N: for h in W, (*) gives A_n sigma(h) = (I + A_h) beta(h, n), which lies in X_1 by (c2),
and X' is spanned by such sigma(h). By (c3), the zeros of sigma modulo X_1 in W are exactly N. By
Lemma 21(a), N lies in the radical, and the system factors through W/N, which has dimension k - 1.
It is anisotropic, so k - 1 <= A(dim X'/X_1) <= A(d). If d <= k - 2, then A(d) = d < k - 1. So
d >= k - 1. Finally d <= dim R = rho, and if rho = k - 1, then X_1 n R = R.

(d) As in the proof of Lemma 30(b), N carries a system with values in X_1 (Lemma 26(a)), span(x0)
is invariant (A_n x0 = 0), and dividing by it and factoring out u (Lemmas 27(a) and 21(a); A_u kills
X_1) leaves an anisotropic system on N/span(u) with values in X_1/span(x0), both of dimension 2.
Its polar form is beta modulo x0. Take n_1, n_2 whose images form a basis as in Lemma 34, and put
a = sigma(n_1), b = sigma(n_2) and delta = beta(n_1, n_2), so that beta(N, N) = span(delta). By
Lemma 21(b) and Proposition 26(e), A_(n_i) kills x0 and sigma(n_i), and (*) gives

    A_(n_1) b = (I + A_(n_2)) delta,     A_(n_2) a = (I + A_(n_1)) delta.

Type (i): beta modulo x0 vanishes, so delta = x0 (delta != 0), and sigma modulo x0 is a linear
bijection, so x0, a, b are independent. Then A_(n_1) b = x0 + A_(n_2) x0 = x0, and likewise
A_(n_2) a = x0. This is (d1); x0 = delta lies in R by (a).
Type (ii): a and b agree modulo x0; replacing n_2 by n_2 + u (which changes b by x0 and not delta)
makes b = a, and delta is not in span(x0, a), so x0, a, delta is a basis of X_1. Now A_(n_2) a =
A_(n_2) b = 0 gives A_(n_1) delta = delta, and A_(n_1) b = A_(n_1) a = 0 gives A_(n_2) delta = delta.
In the basis u, n_1, n_1 + n_2 of N: sigma(n_1 + n_2) = a + a + delta = delta,
beta(n_1, n_1 + n_2) = delta, and A_(n_1 + n_2) kills x0, a and delta. This is (d2), and delta lies
in R by (a). QED

For k = 2, part (c) contains the Remark (k = 2) of tight-cases.md: there, A_v kills X_1, A_w maps X_1
into itself, and Im A_u meets ker A_u.

**Corollary 19.** (a) Let t = 6. In an anisotropic system with dim V = 8, every element of rank 3 in
Case B has Im A_u n ker A_u != 0. More precisely it has one of the shapes (c) with
dim(Im A_u n ker A_u) >= 2, (d1) with x0 in Im A_u, or (d2).
(b) Let t = 7. In an anisotropic system with dim V = 10, an element of rank 3 in Case B on whose U+
beta vanishes has A_u^2 = 0.

*Proof.* (a) is Proposition 27 with k = 3, which needs A(s) = s for s <= 3. (b) is Proposition 27(c4)
with k = 4 and t = 2k - 1, which needs A(s) = s for s <= 4 (Theorem 26). QED

These are necessary conditions. We have not found a contradiction in any of the shapes, so Case B,
and with it A(6) <= 7 and A(7) <= 9, is still open by hand.

## Lemma 35 (a normal form for Case B)

**Lemma 35.** Let (sigma, alpha) be an anisotropic system with dim X = t and dim V = t + k - 1
(k >= 1), and let u be an element with rank A_u <= t - k such that phi(V) = beta(u, V) is a hyperplane
P that does not contain x0 = sigma(u). Then there are bases e_0, ..., e_(t-1) of X and
v_0, ..., v_(t+k-2) of V with

    x0 = e_0,   P = span(e_1, ..., e_(t-1)),   A_u e_c = 0 for c < k,
    v_0 = u,    phi(v_i) = 0 for 1 <= i <= k - 1,   phi(v_(k-1+j)) = e_j for 1 <= j <= t - 1.

*Proof.* ker A_u has dimension at least k and contains x0 (Lemma 21(b)), so it meets the hyperplane
P, which misses x0, in dimension at least k - 1. Take independent e_1, ..., e_(k-1) in P n ker A_u,
extend them to a basis e_1, ..., e_(t-1) of P, and put e_0 = x0. ker phi has dimension
(t + k - 1) - (t - 1) = k and contains u (beta(u, u) = 0); extend v_0 = u to a basis v_0, ..., v_(k-1)
of it, and pick v_(k-1+j) with phi(v_(k-1+j)) = e_j. These t + k - 1 vectors span V. QED

Every element of rank t - k in Case B satisfies the hypotheses, so by Corollary 18 it is enough to
decide whether a system in this normal form exists for (t, k) = (6, 3) and (7, 4).

## The exact search

`cube_groups/case_b.py` takes the CNF of [sat_aniso.py](../cube_groups/sat_aniso.py) (equations (L)
and (Q) for (*), and anisotropy) without its echelon form, and fixes by unit clauses
sigma(v_0) = e_0, beta(v_0, v_i) as in Lemma 35, and the first k columns of A_(v_0). By Lemma 35 the
CNF is satisfiable if and only if some anisotropic system with these (t, k) has such an element.
This fixes sigma(u), all of beta(u, .) and k columns of A_u. The plain encoding had to search over
all of these too, and it did not decide (t, dim V) = (4, 5) within 30 minutes (sat-search.md).
Proposition 27 is not used in the CNF, so an answer does not depend on it.

The run (job m11-caseb-v1, one CPU) had pre-registered predictions: SAT for (t, k) = (2, 1), where
the system below is a model, and UNSAT for (3, 2) (A(3) = 3) and (4, 2) (A(4) = 4). (6, 3), (7, 4)
and (5, 2) were exploratory: UNSAT would give A(6) <= 7, A(7) <= 9, and no Case B element of rank 3
at t = 5. A verified SAT model would be an anisotropic system with dim V > t.

The example for (2, 1): V = span(u, f), A_u = E_11 (it kills e_0 and fixes e_1), A_f = 0,
sigma(u) = e_0, sigma(f) = e_1, beta(u, f) = e_1. It is an anisotropic system (sigma(u + f) = e_0), and
u and u + f satisfy the hypotheses of Lemma 35, while f does not (beta(f, V) = span(e_1) contains
sigma(f)).

## Results (job m11-caseb-v1, 2026-10-17)

The job ran on one CPU from 16:49 to 19:22 UTC on 2026-10-17 (solver CaDiCaL 1.9.5 through
python-sat), with the predictions above written down before it was queued. **Every graded prediction
held:**

| check | predicted | result |
|---|---|---|
| unit tests of case_b.py (6) | pass | pass |
| selfcheck | all true | all true: Lemma 34 (9,216 candidates, 24 systems, 6 + 18, none other); 40 random scrambles of the example, 80 normal forms reached and accepted, 320 one-bit changes all rejected, CNF and brute force agree everywhere |
| (2, 1) | SAT, verified | SAT in 0.22 s (48 variables, 161 clauses); the model is the example above (A_u = E_11, A_f = 0) and passed the brute-force checks; ranks 0, 1, 1 |
| (3, 2) | UNSAT | UNSAT in 0.27 s (666 variables, 3,249 clauses) |
| (4, 2) | UNSAT | UNSAT in 1.02 s (2,252 variables, 12,099 clauses) |

**The open instances were not decided.** (6, 3) reached its 60-minute limit, (7, 4) its 50-minute
limit and (5, 2) its 40-minute limit, all UNKNOWN. So this search settles nothing new: A(6) <= 7,
A(7) <= 9 and Case B at t = 5, rank 3, stay open.

What the run does show:

- The normal form helps a great deal at small sizes. With it, Case B at (t, dim V) = (4, 5) is
  refuted in about a second, while the plain encoding of sat-search.md did not decide (4, 5) (all of
  it, not only Case B) in 30 minutes. The UNSAT answers at (3, 2) and (4, 2) agree with
  Proposition 21 and Theorem 26. They check only the Case B part, and they are computer results
  that rely on the encoding.
- It is not enough at t >= 5. The finer searches in [case-b-shapes.md](case-b-shapes.md) (job
  m12, which also fixes a basis of U+ and its values) and [shape-c.md](shape-c.md) (job m13, which
  also fixes the commuting matrices of Lemma 38, one instance per orbit) are the next attempts. Both
  were waiting for compute when this was written.

The raw results (one JSON file per instance, and the grader's output) are kept with the job's logs,
not in this repository; the numbers above are copied from them. The run can be repeated with the
commands in the module docstring of `cube_groups/case_b.py`.

## Computation

The unit tests of `cube_groups/case_b.py` (which gated this commit) check:

- Lemma 34 by exhaustive search: of the 9,216 choices of A_1, A_2 in M_2(F_2), non-zero sigma(e_1),
  sigma(e_2) and any beta(e_1, e_2), exactly 24 are anisotropic systems, 6 of type (i) and 18 of type
  (ii), and none is of neither type;
- that the example above is an anisotropic system in normal form, that the CNF accepts it, and that
  exactly u and u + f satisfy the hypotheses of Lemma 35;
- on 10 copies of the example in random bases of X and V, that the proof of Lemma 35 (normalise())
  reaches the normal form at both qualifying elements, that the CNF accepts the result, and that on
  one-bit changes of it the CNF agrees with a brute-force check of (*), anisotropy and the normal form;
- that the CNF is sat_aniso's with exactly t + tk + (d - 1)t unit clauses added, and that a system not
  in normal form is rejected.

## Prior work

As for the earlier notes: searches on 2026-10-15 to 2026-10-17 found nothing on the identity (*), on
A(t) or on Question R. The tools are elementary, so a specialist may know them. Please open an issue
at https://github.com/munimtechnologies/kakeya-small-fields if so, or if you find an error.
