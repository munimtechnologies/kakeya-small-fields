# Pre-registration: the Kakeya-restricted entropy LP over F_3

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-18. Made with AI agents working in MV2's name.
Text CC BY 4.0, code Apache-2.0. Written and published before any LP in this search has been
solved. Code: `kakeya_lp.py` (model builder, search driver), `kakeya_cert_check.py`
(independent exact checker), `test_kakeya_lp.py`.

## The question

Note a180 (Theorem 68) proved that every Kakeya set in F_3^n has |K| >= (3^n - 1)^(6/11),
which is base 3^(6/11) = 1.82074. The proof is the Katz-Tao sum-difference inequality: over F_3
a line {a, a+d, a+2d} gives a pair x = a(D), y = a(D) + D with x + y = -(a + 2D), so the three
"readings" x, y, x + y all have entropy at most log|K|. The sum-difference problem knows nothing
else about this pair. A Kakeya pair has two more properties:

1. **3-torsion.** All relations are F_3-linear (2 = -1, 3 = 0). For example x + s = d.
2. **Uniformity (the Kakeya restriction).** The difference D is uniform on the *whole* group, so
   every group-valued variable built in a proof has entropy at most H(D) = log|G|. In the
   general problem such cross terms can be arbitrarily large.

**Question.** Do Shannon inequalities, copy-lemma gluing, F_3-linear closures and the Kakeya
restriction prove (H(x) + H(y) + H(s))/3 >= c log|G| for some c > 6/11?

**The wow if it works:** any such certificate gives a new record lower bound for Kakeya sets
over F_3, |K| >= 3^(c n). Base 1.82074 has stood since note a180. Before that, 9/5 from the
polynomial method (2009-2021) was the best known. Exceeding 0.547541 (base 1.82492) would also
beat what the November 2026 certified sum-difference constants (arXiv:2611.19594, unrefereed)
give through Theorem 68. The conjectured truth is c = 0.57938 (base 1.8899).

## Method (fixed in the code before any solve)

- A configuration (a "word") is a root Kakeya pair plus copy steps. Each step copies a block of
  vertices conditionally on chosen readings (x, y, s or d), independently of all earlier
  variables. Readings are F_3-linear forms in abstract coordinates. The closure of a set of
  forms is its F_3-span plus "x_v, y_v whenever d_v is in the span" (x is a function of d).
- Atoms are the vertex readings and glue readings, plus optional extras (s readings or random
  cross forms r_v +- r_w). There are at most 14 atoms. The LP variables are the entropies of
  closures of atom subsets.
- Rows: all elemental Shannon inequalities over the atoms, the copy-lemma identities, equal-law
  identities inside copied blocks, H(x_v, y_v) = 1, readings = t, and (Kakeya restriction)
  H(atom) <= 1. Objective: minimise t. A rotation argument (in the module docstring) shows that
  the LP value, with all readings set to one t, is a valid lower bound for the average.
- Any LP value above 6/11 + 1e-7 is turned into an exact rational certificate: the
  float duals are rationalised or solved exactly on their support. The certificate must then
  pass `kakeya_cert_check.py`, which shares no code with the builder and uses Fractions only.
- Self-tests, which ship with this note and must pass before it is published: the
  Katz-Tao proof, written as a certificate, gives exactly 6/11 in the checker. The model built
  from the Katz-Tao word contains that proof, using only its own rows. Corrupted certificates
  are rejected. Every row holds exactly on realisations of the construction for explicit Kakeya
  maps of F_3.

## Search plan (job kakeya-lp-v1; 1 CPU, 2 GB, about 150 minutes)

1. Katz-Tao word: base atoms (must give >= 6/11, with the exact certificate checked); plus all
   s readings; plus 2 random cross forms with and without the Kakeya restriction (3 draws).
2. The one-change neighbourhood of the Katz-Tao word: change the root glue, or one page glue to
   any of the 36 one- or two-reading glues. Base atoms first, then cross atoms with the Kakeya
   restriction.
3. Random chains of 3 or 4 page copies (seed 20261118) until the time budget ends.

## Hypotheses and how they are decided

- **H0 (self-test).** The Katz-Tao word gives an LP value >= 6/11, with a checked exact
  certificate. If this fails, the run is void and the bug is fixed first.
- **H1 (3-torsion).** Some word with base atoms only gives a checked certificate above 6/11.
  Prior: unlikely (about 20%) for configurations of this size. Farnamfar needed 30-42 vertices
  for his improvements.
- **H2 (Kakeya restriction).** For some word, adding cross atoms with the Kakeya restriction
  raises the value above the same atoms without it, and above 6/11. Prior: about 15%.
- A **result** is only a certificate that the checker passes with bound > 6/11. Float LP values
  alone are reported as leads, never as theorems.
- A **null result** is also reported: "in these families (N words solved), Shannon + copy +
  F_3 closure + the Kakeya restriction do not beat 6/11". That says where the next attempt
  must look: larger stacked configurations, non-Shannon inequalities, or a non-entropic method.

## Limits

No human mathematician has checked this design. The LP covers only the configurations
listed. Its atom cap (14) excludes the large stacked configurations that carry the 2026
sum-difference records. A null result therefore says nothing about larger configurations.
