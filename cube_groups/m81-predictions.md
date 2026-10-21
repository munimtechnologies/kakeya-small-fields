# Job m81: predictions, written 2026-10-21 ~21:45Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m81 (cube_groups/m81.py) splits two more classes of (B6) at t = 7 and dim V = 9 with d = 1
whose rank-0 sweep was open (job m64a: UNKNOWN at 150 s) by the second matrix A_(v_1)
(Proposition 33, notes/a52.md; counts by job m66). As in m79, the rank-0 instances run too, each
with the 21 negative unit clauses of Lemma 93 (b). Everything but the lists is m69.py, imported
unchanged.

- **m81a:** o009_c005 (|G| = 192, 3839 orbits: 255, 1792, 1792 of rank 0, 1, 2 on X_1): 3839
  instances, 255 with Lemma 93 (b).
- **m81b:** o009_c006 (|G| = 192, 3839: 255, 1792, 1792): the same counts.

**Departure, written before queueing.** m79-predictions.md says the remaining open-sweep classes
get the same treatment once m79's pace is known (median at most 3 s, at most 30 open per class).
m79a and m79b have not run yet. m81a is queued now anyway, next to m79a, m79b and m80 (four
pending), because a free slot would otherwise sit idle and m71a already ran the same kind of class
(d = 1, open sweep) at that pace. m81b stays staged until m79 and m81a are graded. If m79 breaks
the pace rule, m81a's result still counts, but nothing more of this kind is queued before a look
for a hand reduction.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m69.py's check of the group's class, unchanged: m57's 14 checks with the planted control at
   t = 6 in both arms; m66's structure, |G| = Proposition 33 (c), |Adm| = (a), orbit counts by rank
   on X_1 equal to m66's run; every root admissible, of its rank, distinct with its sum with A_u;
   the plan (rank-0 instances present, each with Lemma 93 (b), rank 2 first); hints 79 and units
   49 on the first instance in both arms; the Lemma 93 instance equal to the plain one plus exactly
   21 negative unit clauses, in both arms.
2. m81's own check: the class split here is not among the 27 classes closed by the split, nor
   among the 3 queued in m79.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 33): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses (as for m79, from m71a: every rank-1 and rank-2 instance UNSAT; 13 and 6 of 69 rank-0
instances open at 10 s, all UNSAT at 300 s):

- **Every instance of rank 1 and 2 UNSAT: medium-high confidence.**
- **Some rank-0 instances open after this pass: about 80%;** about 5 to 50 (low confidence), and
  every open instance of rank 0 (medium confidence).
- **The class empty after this one pass: about 15%.**
- **Median UNSAT wall at most 3 s (high confidence).**
- **No SKIPPED instance: about 65%.** 3584 instances of rank 1 and 2 at about 1.1 s take about 66
  minutes; the 255 rank-0 instances could take up to 20 s each (85 minutes) if many run to their
  budgets, which would pass the 150.

Rules:

- **All split instances UNSAT:** the class is empty, (B6) goes up by one, the next corollary.
- **1 to 30 open (SKIPPED counts as open):** re-run each with 5 minutes of CaDiCaL, then 5 of XOR
  (m73's pattern). **More than 30:** read them by rank and by place in m66's order before queueing
  more.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
