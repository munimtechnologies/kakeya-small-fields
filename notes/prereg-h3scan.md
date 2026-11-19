# Pre-registration: h3scan, exhaustive scans for a block of length 3 that beats KLSS over F_3

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-19 (run 20261119T141527Z). Made with AI agents
working in MV2's name. No human mathematician has checked this. Text CC BY 4.0, code Apache-2.0.
Files: `h3scan.py` (reference, exact integers), `h3scan.c` (scanner), `run_h3scan.py` (driver,
grader), `test_h3scan.py`. Job: `h3scan-v1`. Written and filed before any run.

## Question

For P: F_3^3 -> F_3^3 put F_t(x) = P(x) + t x and S(P) = sum_t sum_(fibres F of F_t) |F| log2 |F|
(= 27 Lambda(P) in note a164). By README Theorem 2 the growth base of the smallest Kakeya sets in
F_3^n is at most 3 * 2^(-S(P)/243) for every such P, and the coordinatewise square map gives
S = 162, the base 1.889882 of Kopparty, Lev, Saraf and Sudan (2011), the best known. h_2 = 2 h_1 is
exhaustive (README section 9), so length 3 is the first open block length. Conjecture C_3(3) (a164)
says S(P) <= 162 for every P. a164 proves it for quadratic P that respect a subspace or satisfy
conditions (b) or (c), and says that "q = 3 needs a separate argument" for the rest. Earlier
annealing over all maps (anneal_all.py) found nothing above 162.

**The wow, if it works:** one map with S > 162 would be the first improvement of the F_3 Kakeya
upper bound in 15 years, and would refute C_3(3).

## What the job computes (all exhaustive, no sampling)

1. **quadratic**: every P = Q + L with Q three quadratic forms (3^18) and L a 3x3 matrix. L runs
   over one representative of each class under L -> A L A^-1 + lam I (A in GL_3(F_3), lam in F_3).
   Both moves keep S (conjugation maps fibres to fibres, adding lam x permutes the slices), so this
   covers all 3^27 quadratic maps up to constants. This settles C_3(3) for degree <= 2.
2. **s3**: every S_3-equivariant map of any degree, P(x)_i = f(x_i, {x_j, x_k}) (3^18 maps).
3. **cyclic**: every map P(x) = (f(x), f(sx), f(s^2 x)), s x = (x2, x3, x1), with f of total degree
   <= 3 (16 monomials, 3^16 maps).

C computes S in floating point. Every map with S > 162 - 1e-7 is classified exactly by prime
exponents (equal iff prod |F|^|F| = 2^162). Every map reported above 162, near 162 or in a
family's top 8 values is rebuilt and re-scored in Python with integers.

## Decision rules (fixed now)

- **RECORD**: some map has prod |F|^|F| > 2^162 (exact Python check). Then: an independent
  re-check with a164's `quad3.score_int` in a later job, the implied base 3 * 2^(-S/243), note a189
  and an article. Theorem 2 is our own unrefereed result, so the article must say that the record
  rests on it.
- **NO_GAIN**: all three families complete with max S <= 162. Report: "No quadratic map of F_3^3,
  no S_3-equivariant map, and no cyclic map of degree <= 3 beats KLSS at block length 3." This
  settles C_3(3) for degree 2 (q = 3), closing a164's open q = 3 case. That is a negative result
  and gets a short note, but no article unless it comes with a second result.
- **INCOMPLETE**: a family did not finish. Report only what finished and re-file the rest as -v2.
- Not graded, only reported: the number of maps with S = 162 exactly, the second-best value, and
  whether C and Python agree on every re-checked map. A disagreement voids the run (re-file after
  a fix).

## Prediction (written before the run)

We expect NO_GAIN for the quadratic family (a164's conjecture, together with the October annealing),
and have no prediction for s3 and cyclic.
