# Job m69: predictions, written 2026-10-21 ~06:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m69 (cube_groups/m69.py) runs the first second-matrix splits of (B6) at t = 7 and dim V = 9
(Proposition 33, notes/a52.md; counts by job m66), after job m64a's rank-0 sweep (notes/a57.md),
and re-runs the one split instance of (B5) that job m67a left open.

- **m69a:** r3s_t7_B5_o020_c000_a561 (rank 1 on X_1; UNKNOWN in m67a at an 11.4 s budget, 86 s
  wall) as m67a ran it, 300 s CaDiCaL, then 300 s XOR if open; then the splits of o011_c003,
  o011_c004 and o012_c011 (d = 0; sweep UNSAT, so only rank 1 and 2): 512 + 512 + 510 = 1534.
- **m69b:** the split of o009_c008 (d = 1; sweep UNSAT): 696 of rank 1 and 2; then o004_c001 and
  o006_c001 (d = 2; sweep open at 150 s): 587 each, the 42 of rank 0 with Lemma 93 (b) (21 unit
  clauses: A_(v_2) = 0 on X_1's columns other than x0). 1870 in all.
- Split instances: CaDiCaL, a share of what is left, 10 to 20 s, class by class, most rank first.
  150 minutes per group; instances not reached are SKIPPED and count as open.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks, the planted control at t = 6 in both arms).
2. For each class split: m66's structure (kernel X_1, image R of its pair, rank 3, d by hand),
   G checked element by element, |G| = Proposition 33 (c) = m66's, |Adm| = (a) = m66's, the
   action closed, the tables matching direct conjugation, orbit sizes dividing 2|G| and adding up
   to |Adm|, and the orbit counts by rank on X_1 equal to m66's run.
3. Every root: its m66 index round-trips through m42's mask, it is admissible (Proposition 33
   (a)), its rank on X_1 is the recorded one, and the roots with their sums with A_u are distinct.
4. The plan: per class exactly (rank 1) + (rank 2) instances, plus (rank 0) when the sweep is open;
   Lemma 93 exactly on the rank-0 ones; most rank first; names distinct.
5. Hints and units: the first instance has 79 hints and 49 units in both arms; in m69b the first
   Lemma 93 instance is the plain one plus exactly 21 negative unit clauses on A_(v_2) at X_1's
   columns, consistent, in both arms; a561 has kernel X_1 and image R, is admissible for
   Proposition 32 (a) with rank 1 on X_1, and has 111 hints and 49 units in both arms.
6. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93, Proposition 33 or the sweep rule): re-check by an independent brute force
   before any claim.

## Exploratory, with the decision rules

Guesses (low confidence; no split of a (B6) class with d <= 2 has run before):

- **a561 UNSAT in CaDiCaL within 300 s**, so o020_c000 of (B5) is empty (its other 1614 split
  instances closed in under 10 s each in m67a). Then (B5) stands at 416 of 420.
- **m69a: at least 1500 of 1534 UNSAT; at least one of the three d = 0 classes empty.**
- **m69b: at least 680 of o009_c008's 696 UNSAT; at least 1100 of the 1174 of o004_c001 and
  o006_c001, and at least 70 of their 84 rank-0 instances with Lemma 93.**
- **Median wall time of an UNSAT split instance below 5 s in every class** (the (B5) splits of
  m67a: 1.46 s per instance on average, all under 10 s).
- **Both groups end inside 150 minutes without SKIPPED instances:** a yes, b 50/50.

Rules:

- **All split instances of a class UNSAT** (with the sweep for its rank 0 when dropped): the class
  is empty, (B6) goes up by one, the next corollary.
- **1 to 30 open in a class:** they are re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the
  next job (m70 or later), with the next classes.
- **More than 30 open in a class:** read them by rank first. Rank-0 ones (with Lemma 93) still open
  after both arms get a third-matrix split by hand; rank 1 or 2 ones get a 60 s pass first.
- **Pace:** if the median UNSAT wall time is at most 3 s in a group's classes, the next (B6) jobs
  take 4 or 5 classes per group, smallest first by planned count. If it is above 8 s anywhere, the
  cost of the remaining (B6) split (about 82,000 instances) is re-estimated and written down
  before more of it is queued, and a hand reduction is looked for first.
- **a561 still open after both arms:** a third-matrix split by hand, as m62's rule says.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
