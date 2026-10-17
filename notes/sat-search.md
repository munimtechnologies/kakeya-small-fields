# An exact search for anisotropic systems

MV2 of Munim, Inc., 2026-10-17. Added to kakeya-small-fields after version 1.7.10. This note
describes `cube_groups/sat_aniso.py` and `cube_groups/rank_classes.py`, two exact computer searches
for the anisotropic systems of section 14 of [finite-groups.md](../finite-groups.md) and of
[rank-restriction.md](rank-restriction.md). **Both first full runs have finished:** every graded
prediction that was decided held, but the hard instances ran out of time without an answer. The
split by similarity class (rank_classes.py) decided 4 of the 23 cases for (t, d) = (4, 5) and none
for (5, 6) or (6, 8); see Results. So neither run settles a new case, and A(5) is still open. The
code was researched and written with AI agents working in MV2's name. Its unit tests gate this
commit; they need no SAT solver. No human mathematician has checked it. Text CC BY 4.0, code
Apache-2.0.

## The question

X = F_2^t, V = F_2^d, sigma : V -> X a quadratic map with polar form beta, and alpha : V -> End(X) a
linear map, h -> A_h, with

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

The system is *anisotropic* if sigma(h) != 0 for every h != 0, and A(t) is the largest d for which
one exists. A(t) = t for t <= 4 (Theorem 26 of rank-restriction.md), and 5 <= A(5) <= 6
(Proposition 24). Every open case of Corollary 17 would follow from A(t) = t for every t, and the
first open case, Z_4^10 x Z_2^2, needs only A(7) <= 9.

The searches decide "is there an anisotropic system with these (t, d)?" exactly. They use no lemma
of the notes, only the encoding below, so they also re-check Theorem 26 independently of
Lemma 29 (and so of Theorem 3.5 of de Seguins Pazzis, which Lemma 29 uses).

## The encoding (sat_aniso.py)

Both sides of (*) are linear in h', so (*) holds for all h' if and only if it holds for each basis
vector h' = e_j. Then both sides are polynomials of degree <= 2 in the coordinates of h, and over
F_2 (with h_i^2 = h_i) two such polynomial maps agree on all of V exactly when their coefficients
agree. Write A_i = alpha(e_i), s_i = sigma(e_i) and B_ik = beta(e_i, e_k), with B_ii = 0. The
coefficient of h_i gives (L) and that of h_i h_k gives (Q):

    A_j s_i = (I + A_i) B_ij                    for all i, j                    (L)
    A_j B_ik = A_i B_kj + A_k B_ij              for i < k and j not in {i, k}   (Q)

(For j in {i, k} the coefficient of h_i h_k gives an identity.) So the systems on V are exactly
the tuples (A_i, s_i, B_ik) of matrices and vectors over F_2 satisfying (L) and (Q), and sigma is
recovered as sigma(h) = sum h_i s_i + sum over i < k of h_i h_k B_ik. Anisotropy is one clause per
non-zero h: some coordinate of sigma(h) is 1.

GL(X) acts on systems (A_h -> g A_h g^-1, sigma -> g sigma, beta -> g beta), and the action
preserves (*) and anisotropy. So the values s_1, ..., s_d may be put in echelon form: each s_i is
either the next unit vector e_r (r the rank of s_1, ..., s_(i-1)) or lies in the span of
e_0, ..., e_(r-1). The CNF encodes products and parities with Tseitin variables, and an
UNSAT answer means no anisotropic system with these (t, d) exists, that is A(t) < d.

Every SAT answer is decoded and re-checked by brute force: (*) on all pairs (h, h'), and
sigma(h) != 0 for all h != 0. That check does not use (L) or (Q). The selfcheck and unit tests
compare (L) + (Q) with the brute-force check, and compare the CNF with it, on known examples
(Example 1, the linear systems, two copies of the norm form of F_4, which is anisotropic but not a
system) and on random systems, their anisotropic restrictions and one-bit mutations of each.

## Splitting by one element (rank_classes.py)

A single CNF for t = 5 and d = 6 may be too hard, so rank_classes.py splits it. Take an anisotropic
system and any u != 0, and choose a basis of V with e_1 = u. A change of basis g of X makes
A_(e_1) = g A_u g^-1 a fixed representative C of the similarity class of A_u. Then s_1 = sigma(e_1)
lies in ker C (put h' = h in (*): A_h sigma(h) = 0, since beta is alternating), and an invertible
z commuting with C keeps A_(e_1) = C and moves s_1 to z s_1. So s_1 may be taken to be the least
vector of its orbit under the centraliser. Hence

    an anisotropic system (t, d) with an element similar to C exists
        iff  one of the SAT calls (A_(e_1) = C, s_1 = r) is satisfiable,

with r running over orbit representatives in ker C \ {0}. For C = 0 the whole of GL(X) commutes
with C, and the echelon form above is used instead. Every A_h of an anisotropic system is singular
(A_h sigma(h) = 0 with sigma(h) != 0), so the calls for all singular classes together decide
whether A(t) >= d. The calls for the classes of one rank decide whether some anisotropic system
(t, d) has an element of that rank.

The classes come from rational canonical forms: a class of t x t matrices over F_2 is a choice of a
partition for each monic irreducible polynomial p, with the sizes weighted by deg p adding up to t.
The representative is block diagonal with the companion matrix of p^m for each part m, and its rank
is t minus the number of parts at p = x. The unit tests check the class counts (2, 6, 14, 34, 74
for t = 1, ..., 5, the number of conjugacy classes of M_t(F_2)) and compare the representatives with
the orbits of GL(t, F_2) found by brute force for t <= 3 (the selfcheck goes to t = 4). They also
check the centraliser against brute force for t = 3, and that after normalisation the class CNF
accepts exactly the anisotropic systems, on random examples.

## What the runs test

Both runs were queued on 2026-10-17 with these predictions written down before they ran:

- **sat_aniso.py:** SAT with verified models for (t, d) = (1, 1), ..., (5, 5) (positive controls);
  UNSAT for (1, 2), (2, 3), (3, 4), (2, 4) and (4, 5), the last re-checked with a second solver. A
  control without (*) (two copies of the norm form) must be SAT for (t, d) = (2, 4). (5, 6) and
  (6, 7) are exploratory, with time limits.
- **rank_classes.py:** for (4, 5), every instance of every singular class UNSAT, which would give a
  lemma-free computer proof of A(4) = 4. For (5, 6), every instance of rank 4 UNSAT (Lemma 30: an
  element of rank t - 1 gives dim V <= t). The instances of ranks 0 to 3 for (5, 6), and of rank 3
  for (6, 8), are exploratory. If every singular class for (5, 6) is UNSAT, then A(5) = 5, and
  M(5) = 5 by Theorem 24.

A verified SAT answer for (4, 5) would refute Theorem 26, and we would withdraw it here. A verified
SAT answer for (5, 6) would be the first anisotropic system with dim V > t. It would be published
with its matrices.

## Results

**sat_aniso.py** (run on 2026-10-17 from 10:05 to 12:36 UTC, one CPU, 1 GB, python-sat with
CaDiCaL 1.9.5 unless Glucose 4 is named; wall-clock seconds per instance). The 9 unit tests passed. The selfcheck passed: on 160 cases (98
systems, 60 of them anisotropic) the coefficient equations, the CNF and the echelon normalisation
agreed with the brute-force check every time.

    (t, d)            prediction           result                        seconds
    (1,1) ... (5,5)   SAT, verified        SAT, model verified           < 0.5 each
    (2,4) without (*) SAT, anisotropic     SAT, anisotropic, not (*)     0.2
    (1,2)             UNSAT                UNSAT                         0.2
    (2,3)             UNSAT                UNSAT                         0.2
    (3,4)             UNSAT                UNSAT                         0.3
    (3,4) Glucose 4   UNSAT                UNSAT                         0.3
    (2,4)             UNSAT                UNSAT                         0.2
    (4,5)             UNSAT                UNKNOWN (budget 30 min)       1800
    (4,5) Glucose 4   UNSAT                UNKNOWN (budget 15 min)       900
    (5,6)             exploratory          UNKNOWN (budget 90 min)       5400
    (6,7)             exploratory          UNKNOWN (budget 15 min)       900

Every graded prediction that was decided held (11 of 11). The prediction for (4, 5) was not
decided, so the plain search gives no second proof of A(4) = 4; we had guessed it would take under
five minutes, and that guess was wrong. The step from d = t to d = t + 1 is where the plain encoding
becomes hard. That is why rank_classes.py splits the search by the class of one element.

**rank_classes.py** (run on 2026-10-17 from 12:57 to 15:54 UTC, one CPU, 1 GB, CaDiCaL 1.9.5; job
m8-rank-classes-v1). The 11 unit tests passed. The selfcheck passed: the class counts for
t = 1, ..., 5 are 2, 6, 14, 34, 74 (singular 1, 3, 8, 20, 47); the ranks of the 74 classes for t = 5
are 0: 1, 1: 2, 2: 6, 3: 13, 4: 25, 5: 27; there are 14 classes of rank 3 for t = 6; the
representatives agree with the GL(t, 2) orbits found by brute force for t = 1, ..., 4; and on 120
random cases (39 accepted, 17 classes hit) the normalised class CNF agreed with the brute-force
check every time. The instance counts were as predicted: 23 for (4, 5), and 25, 19 and 13 for
(5, 6) at rank 4, rank 3 and ranks 0 to 2. Each group of instances had a total time budget, and
instances left when it ran out are SKIPPED.

    (t, d)  ranks   budget per instance / group   UNSAT   UNKNOWN   SKIPPED   SAT
    (3,3)   0       2 / 4 min (positive control)  -       -         -         1, verified
    (5,5)   0       4 / 5 min (positive control)  -       -         -         1, verified
    (4,5)   0-3     3 / 30 min                    4       8         11        0
    (5,6)   4       2 / 20 min                    0       10        15        0
    (5,6)   3       8 / 75 min                    0       10        9         0
    (5,6)   0-2     5 / 30 min                    0       6         7         0
    (6,8)   3       2 / 20 min                    0       10        12        0

The four decided instances for (4, 5) are rank-3 classes (classes 14, 20, 21 and 22 of the run's
list), solved in 166, 107, 147 and 63 seconds; the other rank-3 classes reached the 3-minute limit.
So every graded prediction that was decided held (the selfcheck, the unit tests, both positive
controls and 4 of the 23 instances for (4, 5)), and no instance anywhere came back SAT. But the
predictions that mattered were not decided: there is no lemma-free proof of A(4) = 4, no answer for
rank 4 at (5, 6), and nothing on A(5) or Question R. Our exploratory guess that each (4, 5) instance
would take under a minute was wrong. Fixing one matrix to its rational canonical form is not enough
symmetry breaking for one CPU. The searches of [case-b.md](case-b.md) and
[case-b-shapes.md](case-b-shapes.md) fix much more (sigma(u), all of beta(u, .), part of A_u, and a
basis of U+ with its values) and target only the configuration that Corollary 18 leaves open; their
runs are queued.

## An open question the runs probe

Lemma 30 gives dim V <= t + A(t - rho - 1) for an element of rank rho. Every bound in the table of
Proposition 24 from t = 5 to 11 comes from its case rho = 3. A sharper form would move them:

**Question R.** In an anisotropic system, does an element of rank rho >= 1 give
dim V <= t + A(t - rho - 2) (reading A(-1) as 0)? In particular, does an element of rank t - 2 give
dim V <= t?

For t <= 4 the answer is yes, because A(t) = t there. For t = 5, a yes for rank 3 = t - 2 would give
A(5) = 5 through the remark after Proposition 24. With rho = 3 and t = 7 it would give A(7) <= 9,
which settles Z_4^10 x Z_2^2. The run of rank_classes.py did not decide any instance for (5, 6) at
rank 3 or for (6, 8) at rank 3 (see Results), so Question R is open for t = 5 and t = 6. We have no
proof of Question R. In the case t - rho = 2 with
dim V = t + 1, the proof of Lemma 30 forces codim U+ = t - 1 and U+ = span(u, v) with sigma(v)
outside span(sigma(u)). Then either beta(u, .) maps V onto X with kernel span(u), or its image is a
hyperplane that misses sigma(u), with kernel span(u, v). In the second case A_v also kills
ker A_u, so every element of span(u, v) has rank <= t - 2. [question-r.md](question-r.md) shows
that the first case needs t >= 5 and pins down its shape at t = 5 (Proposition 25).
[tight-cases.md](tight-cases.md) extends the two cases to every rank and shows that the first case
needs 2 rho >= t + 1. So at t = 6 and t = 7 only the second case stands between Proposition 24 and
A(6) <= 7 and A(7) <= 9 (Corollary 18). We have found no contradiction in the second case.

## Running it

    pip install python-sat
    python cube_groups/sat_aniso.py --part selfcheck --out-dir out
    python cube_groups/sat_aniso.py --part solve --t 4 --d 5 --budget-minutes 30 --out-dir out
    python cube_groups/rank_classes.py --part selfcheck --out-dir out
    python cube_groups/rank_classes.py --part solve --t 5 --d 6 --ranks 3 --budget-minutes 8 --total-minutes 75 --out-dir out
    python -m unittest discover -s cube_groups -p "test_*.py"

Each instance is solved in a child process with a wall-clock budget, and an instance that runs out
of time is reported as UNKNOWN, not as UNSAT. The solvers are CaDiCaL and Glucose through PySAT.

Please open an issue at https://github.com/munimtechnologies/kakeya-small-fields if you find an
error, or if anisotropic systems or Question R are known.
