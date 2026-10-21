# Job m67: predictions, written 2026-10-21 ~04:50Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m67 (cube_groups/m67.py) is the next pass over (B5) at t = 7 and dim V = 9 after jobs m63a,
m64b and m66 reported (notes/a56.md). It replaces job m63b, which was staged and never queued:

- m64b's sweep closed the rank-0 case of r3b_t7_B5_o000_c002, so by m64-predictions.md's rule ("a
  class whose split is already running: its rank-0 instances count as closed by the sweep") the 20
  rank-0 tail instances that m62b left open are closed. Of m63b's plan, what still matters is the 5
  tail instances of rank 1 or 2 (m63.TAIL_PLAIN["b"]) and the 7 controls of m63's speed rule.
- **m67a:** the 5, as m62's instances unchanged (300 s CaDiCaL, then 300 s XOR if open), then the
  split of r3b_t7_B5_o020_c000 without its 51 rank-0 instances (its sweep was UNSAT in 62 s):
  900 of rank 1 and 715 of rank 2, 1615 instances, CaDiCaL at 10 to 20 s each, rank 2 first.
- **m67b:** m63b's 7 controls (m62b's re-opened rank-0 instances of o000_c000, a known-empty class,
  with Lemma 93's 42 unit clauses; 300 s + 300 s), then the whole split of r3b_t7_B5_o002_c001
  (its sweep stayed open at 600 s in both arms): 475 of rank 2 and 1182 of rank 1 as m62's
  instances, then 251 of rank 0 with Lemma 93, 1908 instances, CaDiCaL at 10 to 20 s each.
- 150 minutes per group; instances not reached are SKIPPED and count as open.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m60.py's check of the group, unchanged: m57.py's 14 checks (the planted control at t = 6 in
   both arms), m55's structure, |G|, |Adm| and class counts by rank on X_1 for both classes used
   (o000_c002 1827 and o020_c000 1666 in a; o000_c000 671 and o002_c001 1908 in b), every
   representative admissible with its recorded rank, the named rows recomputed, hint and unit
   counts of one instance in each arm.
2. The named rows: 5 of rank 1 or 2 from o000_c002 (a), 7 of rank 0 from o000_c000 (b), each one
   of m55's representatives with its recorded index, rank and A_(h_1). In a, m62b's 1802 + the 20
   rank-0 + these 5 = 1827.
3. The split plan: 1615 (a) or 1908 (b) instances, all of the tail class, distinct, most rank first,
   Lemma 93 exactly on the rank-0 ones, none of rank 0 in a.
4. In b, on the first rank-0 split instance, in both arms: the Lemma 93 instance is m62's instance
   followed by exactly 42 negative unit clauses on A_(v_2), A_(v_3) at X_1's columns, consistent.
5. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or the sweep rule): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses (low confidence):

- **m67a: all 5 named UNSAT in CaDiCaL**, so o000_c002 is empty. m63a's 3 analogous instances
  closed in about 1 s each.
- **m67a: at least 1600 of 1615 UNSAT** at 10 to 20 s. Rank 1 and 2 instances closed 1452 of 1455
  (o000_c001) and 1479 of 1484 (o000_c002) at these budgets. o020_c000 empty: guess no (1 to 15
  open), low confidence.
- **m67b: all 7 controls UNSAT in CaDiCaL, and m63's speed rule over its 13 controls (m63a's 6
  and these 7) gives "adopt"** (median ratio m63/m62 below 0.5, none slower by more than 2 times).
  On m63a's 5 decided controls alone the median is 0.337.
- **m67b: at least 1850 of 1908 UNSAT, and at least 240 of the 251 rank-0 ones.** m62's rank-0
  instances without Lemma 93 closed 319 and 323 of 343 at these budgets; with it, m63a closed 24 of
  24 open ones in at most 92 s.
- **Both groups end inside 150 minutes without SKIPPED instances:** yes for a, 50/50 for b.

Rules:

- **All named and tail instances of a class UNSAT** (with the sweep for o020_c000's rank 0): the
  class is empty, (B5) goes up by one, the next corollary.
- **1 to 30 open in a split:** they are re-run with 5 minutes of CaDiCaL, then 5 of XOR (rank-0
  ones with Lemma 93), in the next job (m68).
- **More than 30 open:** read them by rank first; rank-0 ones still open after both arms get the
  third-matrix split by hand first, as m62's rule says.
- **Speed rule "adopt":** later (B5) and (B6) split jobs carry Lemma 93 on every rank-0 instance,
  and a clausal form of "rank at most 1 on X_1" for rank-1 instances is designed (m63's rule).
  "keep_for_open" or "fact_only": as m63-predictions.md says.

No speed-up is claimed before the run. Every UNSAT is a solver answer saved without a proof
certificate. An UNKNOWN is not evidence either way.
