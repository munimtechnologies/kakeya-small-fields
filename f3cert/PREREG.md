# f3cert: do characteristic-3 entropy certificates raise the Kakeya lower bound over F_3?

Pre-registered 2026-11-27 by MV2 of Munim, Inc. (mv2@munimtech.com), before any LP was solved.
Made with AI agents working in MV2's name; no human mathematician has checked it.
Code Apache-2.0, text CC BY 4.0.

## Question

Let beta_3 = lim K(n,3)^(1/n) be the growth base of the smallest Kakeya sets in F_3^n.
Kopparty, Lev, Saraf and Sudan ([arXiv:1003.3736](https://arxiv.org/abs/1003.3736)) proved
1.8 <= beta_3 <= 3/2^(2/3) = 1.88988 and called q = 3 the most intriguing case. A Kakeya set gives
a pair (x, y) of F_3^n-valued random variables whose difference d = x - y is uniform on the non-zero
vectors and determines the pair, with x, y and -(x + y) in the set. So any bound
H(x - y) <= C max(H(x), H(y), H(x + y)) gives beta_3 >= 3^(1/C). The Katz-Tao exponent C = 11/6
gives 1.82074. Farnamfar's record C = 1.8263483657 for every abelian group without 2-torsion
([arXiv:2611.19594](https://arxiv.org/abs/2611.19594), 14 Nov 2026, building on T. S. Tomar,
[Zenodo 10.5281/zenodo.23687856](https://doi.org/10.5281/zenodo.23687856)) gives **1.82492**, the
best lower bound we know of for beta_3.

General groups cannot do better than C = 1.77898 (Lemm's construction). In characteristic 3, though,
the conjectured truth is C = log 27 / log(27/4) = 1.72598 (Conjecture R3, ours, unrefereed), so there
is room. **Does the characteristic-3 structure, which Farnamfar's and Tomar's certificates never
use, give a better certificate on the same stacked configurations?**

## Method (f3cert.py)

1. Download Farnamfar's public certificates `standard-five-page.json` (C = 152/83, 30 vertices)
   and `standard.json` (C = 2762/1509, 108 vertices) from the arXiv ancillary files (CC BY 4.0).
   Record their SHA-256.
2. Rebuild every configuration as F_3-linear forms in symbols. Copying vertices U over glue
   readings V adds one new symbol per vector of a complement of span(V) in span(U). This reproduces
   Tomar's page z0..z5 = (a,b), (a,c), (d,b), (d,c), (e,a+b-e), (e,c) exactly (tested).
3. Entropy classes are F_3-spans closed under difference-injectivity (d_v in T => x_v, y_v in T).
   Classes are merged by equal-law identifications of copies, found on demand plus the certificate's
   own `eqlaw` list.
4. **Control (exact):** replay each certificate's rational identity on these classes. It must
   leave zero residual on every class, and the LP with its own rows and weights must certify
   value >= 1.
5. LP variants (scipy HiGHS), all with h(d0) = 1 and, by the rotation trick below, h(x0) = h(y0) = h(s0) = w:
   - `cert-sym-plain`: the certificate's rows only;
   - `cert-sym-meet`: plus submodularity through intersections, h(A) + h(B) >= h(A + B) + h(A cap B),
     and monotonicity;
   - `cert-sym-meet-unif`: plus the uniform bound h(T) <= dim_F3(T) (every form takes values in
     F_3^n while d is uniform; Kakeya-specific);
   - `aug-*`: plus extra rows (all pairs of reading lines and, on the 30-vertex page, the cross lines
     f + g and f - g; neighbours of every certificate row).
6. Every reported bound is **exact**: the dual solution is converted to rationals and the bound is
   recomputed in exact arithmetic from the rows and the variable bounds, so floating-point error
   can only lower it.

Rotation trick (characteristic 3): for any pair (x, y), the triple (x, y, -(x + y)) has all three
cyclic differences equal to d. Products of independent rotated copies therefore have equal entropies
for x, y and x + y and a uniform difference, so the symmetric LP bounds the Kakeya problem.

## Built-in alarms

- `CONTROL_FAIL`: the replay or the control LP fails. Then the reconstruction is wrong and no
  number is reported as a bound.
- `UNSOUND`: any symmetric LP certifies w above 0.5793802 (the KLSS witness value, 3^w = 1.88988).
  Real distributions satisfy every row, so this would mean a modelling bug.
- The unit tests carry out the conditional copies exactly on real distributions
  ((x, y) = (f(d), f(d) - d) with d uniform on F_3 or F_3^2). They check every class, row,
  closure and uniform bound on those distributions.

## Outcomes (fixed now)

- `F3_RECORD`: a certified w > 1/1.8263483657186 = 0.547540, i.e. beta_3 > 1.82492. That would be the
  first characteristic-3 improvement and a new lower bound for the Kakeya constant over F_3. Before
  any claim, the exported certificate is re-checked by an independent implementation in a later
  run, and prior work is searched again.
- `F3_GAIN`: above the certificate's own general-group value (83/152 or 1509/2762) but not above
  the record. Characteristic 3 helps; the next step is the record configurations.
- `NO_GAIN`: no variant beats the certificate's own value. This is an honest negative: on these
  configurations, characteristic 3 adds nothing.

## Limits

Only Shannon inequalities, conditional copies and the uniform bound are used, on Farnamfar's
standard (non-record) configurations. The record configurations use cross forms and non-Shannon
lemmas and are not attempted here. The link beta_3 >= 3^w uses the sum-difference reduction
(kakeya-small-fields a181), which is not human-checked.
