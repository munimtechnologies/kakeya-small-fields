# Job m70: predictions, written 2026-10-21 ~07:55Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m70 (cube_groups/m70.py) continues the second-matrix splits of (B6) at t = 7 and dim V = 9
(Proposition 33, notes/a52.md) after job m69a, and re-runs the 27 split instances of (B5) that job
m67b left open (notes/a58.md). Everything but the lists and the checks of the 27 is m69.py,
imported unchanged.

- **m70a:** the 27 open instances of r3b_t7_B5_o002_c001 (10 of rank 1 on X_1, 17 of rank 0 with
  Lemma 93's 42 unit clauses), each 300 s of CaDiCaL, then 300 s of XOR if open; then the splits of
  o011_c002 (d = 0, sweep UNSAT: 924 of rank 1 and 2), o004_c000 and o006_c000 (d = 2, sweep open:
  674 each, 51 of rank 0 with Lemma 93 (b)). 2272 split instances.
- **m70b:** the splits of o008_c004 (d = 1, sweep open: 747, 51 of rank 0), o003_c002, o003_c003
  and o003_c004 (d = 2, sweep open: 847 each, 135 of rank 0). 3288 split instances.
- m69's pace rule asked for 4 or 5 classes per group (median UNSAT wall 1.22 to 1.27 s in m69a).
  m70a takes 3 because its 27 re-runs may need up to 270 minutes at worst; this is a deliberate
  departure, written down here before the run.
- Job m69b (o009_c008, o004_c001, o006_c001) was still pending when m70 was written; m70 splits none
  of its classes.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of each group, unchanged (m57's 14 checks with the planted control at t = 6 in
   both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank on X_1
   equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u; the
   plan; hints 79 and units 49 on the first instance in both arms; the first Lemma 93 instance of
   (B6) = the plain one + 21 unit clauses, in both arms). No class split is one closed before.
2. m70a, the 27: o002_c001's A_u has kernel X_1, image R, rank 3 and d = 3; 10 of rank 1 and 17 of
   rank 0, rank 1 first; every A_(v_1) admissible for Proposition 32 (a) with its recorded rank;
   Lemma 93 exactly on the rank-0 ones; 54 distinct maps with their sums with A_u; 111 hints and 49
   (or 49 + 42) units in both arms; the first Lemma 93 instance = the plain one + 42 unit clauses.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93, Proposition 32 or 33 or the sweep rule): re-check by an independent brute
   force before any claim.

## Exploratory, with the decision rules

Guesses (low confidence unless said):

- **m70a: at least 25 of the 27 UNSAT in CaDiCaL within 300 s; o002_c001 empty: yes, medium
  confidence.** a561 (open at 11.4 s in m67a) closed in 1.37 s in m69a; m63a closed 24 of 24
  re-opened rank-0 instances with Lemma 93 in at most 92 s.
- **o011_c002 empty (high confidence):** all three d = 0 classes split in m69a were, every
  instance under 2.7 s.
- **o004_c000 and o006_c000: at least 640 of 674 UNSAT each; at least one of them empty: 50/50.**
  These and m70b's are among the first (B6) splits with d = 2 or with rank-0 instances.
- **m70b: at least 720 of 747 for o008_c004 and at least 800 of 847 for each o003 class.**
- **Median UNSAT wall at most 3 s in every class; the rank-0 (Lemma 93) instances have a higher
  median than the rank 1 and 2 ones in every d = 2 class.**
- **No SKIPPED instance:** m70a yes (unless the 27 take over 60 minutes), m70b 50/50.

Rules:

- **All split instances of a class UNSAT** (with the sweep for its rank 0 when dropped): the class
  is empty, (B6) goes up by one, the next corollary. **All 27 UNSAT:** o002_c001 is empty, (B5) goes
  up by one.
- **1 to 30 open in a class:** re-run with 5 minutes of CaDiCaL, then 5 of XOR, in the next job.
- **More than 30 open in a class:** read them by rank first; rank-0 ones (with Lemma 93) still open
  after both arms get a third-matrix split by hand; rank 1 or 2 ones get a 60 s pass first.
- **Any of the 27 still open after both arms:** a third-matrix split by hand (m62's rule).
- **Pace:** median UNSAT wall at most 3 s in a group's classes: the next (B6) jobs keep 4 or 5
  classes per group. Above 8 s anywhere: re-estimate the cost of the rest of the (B6) split and
  look for a hand reduction before queueing more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
