# Job m60: predictions, written 2026-10-20 ~22:10Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m60 (cube_groups/m60.py) carries out the rules that job m59 wrote down before it ran
(m59-predictions.md). The setting is in notes/a45.md, a48.md and a49.md.

## What m59b found (graded 2026-10-20 ~21:50Z, all 27 checks held, no SAT)

- r3b_t7_B5_o009_c009 and o016_c024 (d = 1): UNSAT in 10.9 s and 31.9 s of XOR. Guess (at least 1
  of 2) held. (B5) goes to 409 of 420.
- Split of o001_c000: 436 of 445 UNSAT; open 9, all of rank 0 on X_1 (a025, a085, a096, a117, a153,
  a207, a210, a214, a227). Guess (420 to 445) held.
- Split of o002_c000: 404 of 421 UNSAT; open 17: 15 of rank 0, 2 of rank 1 (a219, a262). Guess (400
  to 421) held.
- The open instances of o002_c000 had budgets of 10.5 to 15.4 s, not 20 s: m59's shared budget split
  148 minutes over 866 instances, and o002_c000 ran first. Those of o001_c000 had 18.9 to 20 s.

So m59's rule applies to both classes: 1 to 30 open, re-run them with 5 minutes of CaDiCaL then 5 of
XOR.

## The plan

- m60a: the 9 open of o001_c000 and a025, a085, a096, a117 of o002_c000 (13 instances, at most 130
  minutes), then the split of r3b_t7_B5_o032_c000 (856 instances, m55's 18 / 387 / 451 by rank on
  X_1) with CaDiCaL at most 20 s each in the time left of 150 minutes.
- m60b: the other 13 open of o002_c000, then the split of r3b_t7_B5_o000_c000 (671 instances,
  133 / 416 / 122) the same way.
- In both splits the instances of rank 2 on X_1 run first, then rank 1, then rank 0, so the slow
  kind gets the larger share of what is left. Instances that the time does not reach are SKIPPED and
  count as open.

o032_c000 is the first split with X_1 = span(e_0, e_1, e_2, e_6), not inside H0. m57.rank_on_x1
reads columns 0 to 3, which is right only for X_1 = span(e_0, ..., e_3), so m60 takes the rank on
the columns at X_1's own basis vectors (rank_on) and checks that it equals m57.rank_on_x1 on every
representative of the three classes with X_1 = span(e_0, ..., e_3), and m55's rank for every
representative of all four.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks).
2. For every class used: m55's structure, |G| = the hand order, |Adm| = the hand count, closed
   action, and m55's counts: o001_c000 445 = 67 / 268 / 110, o002_c000 421 = 64 / 257 / 100,
   o032_c000 856 = 18 / 387 / 451, o000_c000 671 = 133 / 416 / 122.
3. Every representative is in Adm of Proposition 32 (a) with rank_on on its own X_1, of the recorded
   rank, and distinct with its sum with A_u; rank_on equals m57.rank_on_x1 where X_1 = span(e_0, ...,
   e_3).
4. Each of the 26 re-opened instances is recomputed with the m55 index, rank and A_(h_1) that m59b
   ran (copied into m60.py from m59b's output).
5. One re-opened instance in the XOR arm and one tail instance in the CNF arm: 111 hints, 49
   consistent unit clauses (and XOR constraints in the XOR arm).
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u and A_(v_1) as
   fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **Re-opened: at least 20 of 26 UNSAT in the 5 minutes of CaDiCaL, at least 23 of 26 after both
  arms.** The B6 instance a025 of kind graph (rank 0 too) closed in 157 s of CaDiCaL, and o002's
  open ones had only 10 to 15 s.
- **o001_c000: all 9 UNSAT, so the class is empty.**
- **o032_c000: 830 to 856 of 856 UNSAT at 20 s, the open ones of rank 0 or skipped.** It has only
  18 instances of rank 0.
- **o000_c000: 600 to 671 of 671 UNSAT at 20 s, the open ones mostly of rank 0.** It has 133 of
  rank 0, the most of any split so far.
- **Both groups end inside 150 minutes, the re-opened part inside 60.**

Rules:

- **A (B5) class all of whose instances are UNSAT (m59b with m60a and m60b for o002_c000):** the
  class is empty; (B5) goes up by one per class.
- **A re-opened instance still open after both arms:** count the third-matrix split for it by hand
  (A_(h_2) up to the stabiliser of A_u and A_(h_1)) before any longer run, as m59's rule for kind
  graph.
- **A split (o032_c000 or o000_c000) with 1 to 30 open (SKIPPED included):** re-run them with 5
  minutes of CaDiCaL then 5 of XOR. **More than 30:** a 60 s pass first, then the same.
- Next (B5) d = 3 splits after this: o000_c001 (1798), o000_c002 (1827), o002_c001 (1908),
  o020_c000 (1666), then o031_c000 (3366) and o033_c000 (2306).
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

## Observations written down before the run (not graded)

- r3b_t7_B5_o002_c000 has the same A_u (34086976) and R as the kind-graph class of (B6), and its
  open a117 and a153 have the same A_(h_1) as (B6)'s open r3g_t7_B6_o002_a117 and a153 (now in job
  m59a). r3b_t7_B5_o000_c000 has the same A_u (266304) as (B6)'s kind-L class. The instances differ
  (p = 5 against p = 6), so this is a pairing to watch, not a reduction.
- At the 16 values of k from 25 to 262 that were compared (the open ones of either class), the k-th
  representatives of o001_c000 and o002_c000 have the same m55 index; at k = 338 they do not. The 9
  open of o001_c000 are among the 17 open of o002_c000.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
