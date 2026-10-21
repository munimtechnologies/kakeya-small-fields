# Job m62: predictions, written 2026-10-20 ~23:55Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m62 (cube_groups/m62.py) carries out the rules that job m60 wrote down before it ran
(m60-predictions.md). The setting is in notes/a45.md, a48.md to a51.md.

## What m60 found (graded 2026-10-20 ~23:35Z, every graded check held, no SAT)

- m60a: all 9 open of r3b_t7_B5_o001_c000 UNSAT in CaDiCaL (32 to 222 s), so that class is
  empty. a025, a085, a096, a117 of o002_c000 UNSAT in CaDiCaL (15 to 121 s).
- m60b: the other 13 open of o002_c000 UNSAT, 11 in CaDiCaL (13 to 271 s) and a207, a227 in XOR
  (57 s, 63 s) after 300 s of CaDiCaL. With m59b's 404 and m60a's 4 that is 421 of 421, so
  o002_c000 is empty. (B5) goes from 409 to 411 of 420.
- Split of r3b_t7_B5_o032_c000: 851 of 856 UNSAT at 20 s; open a014, a023, a053, a083 (rank 0 on
  X_1) and a574 (rank 1). Split of o000_c000: 662 of 671; open a031, a098, a123, a155, a162, a273,
  a277, a308, a363, all rank 0. Every open one had its full 20 s.
- Guesses: re-opened 24 of 26 in CaDiCaL (guess at least 20) and 26 of 26 with XOR (guess at least
  23); o001_c000 empty (held); 851 in 830 to 856 (held); 662 in 600 to 671 (held); both groups
  inside 150 minutes (42 and 45 minutes) and each re-opened part about 21 minutes (held).

So m60's rule applies to both splits: 1 to 30 open, re-run them with 5 minutes of CaDiCaL then 5
of XOR.

## The plan

- m62a: o032_c000's 5 open and o000_c000's a031, a098 (7 instances, at most 70 minutes), then the
  split of r3b_t7_B5_o000_c001 (1798 instances, m55's 343 / 1136 / 319 by rank on X_1) with
  CaDiCaL at most 20 s each in the time left of 150 minutes.
- m62b: o000_c000's other 7 open, then the split of r3b_t7_B5_o000_c002 (1827 instances,
  343 / 1164 / 320) the same way.
- As in m60, split instances run rank 2 first, then 1, then 0. The shared budget is
  min(20 s, max(10 s, time left / instances left)), so early instances may get 10 s, not 20:
  read budget_seconds before calling an UNKNOWN hard. Instances not reached are SKIPPED and count
  as open.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks).
2. For every class used: m55's structure, |G| = the hand order, |Adm| = the hand count, closed
   action, and m55's counts: o032_c000 856 = 18 / 387 / 451, o000_c000 671 = 133 / 416 / 122,
   o000_c001 1798 = 343 / 1136 / 319, o000_c002 1827 = 343 / 1164 / 320.
3. Every representative is in Adm of Proposition 32 (a), of the recorded rank on its own X_1, and
   distinct with its sum with A_u; rank_on equals m57.rank_on_x1 where X_1 = span(e_0, ..., e_3).
4. Each of the 14 re-opened instances is recomputed with the m55 index, rank and A_(h_1) that m60
   ran (copied into m62.py from m60's output).
5. One re-opened instance in the XOR arm and one tail instance in the CNF arm: 111 hints, 49
   consistent unit clauses (and XOR constraints in the XOR arm).
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u and A_(v_1) as
   fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **Re-opened: at least 10 of 14 UNSAT in the 5 minutes of CaDiCaL, at least 12 of 14 after both
  arms.** In m60 the instances that had their full 20 s before (o001_c000's) all closed in CaDiCaL
  in 33 to 222 s; these also had 20 s, but two of m60b's needed XOR.
- **o032_c000 empty (all 5 UNSAT); o000_c000 empty needs all 9 over both jobs: guess yes, low
  confidence.**
- **o000_c001: 1740 to 1798 of 1798 UNSAT; o000_c002: 1770 to 1827 of 1827.** The open ones of rank
  0 or skipped. They have 343 instances of rank 0 each, the most of any split so far (o000_c000
  had 133 and left 9 open).
- **Both groups end inside 150 minutes, the re-opened part inside 50.**

Rules:

- **A (B5) class all of whose instances are UNSAT** (o032_c000 from m62a alone; o000_c000 needs
  m62a and m62b): the class is empty; (B5) goes up by one per class.
- **A re-opened instance still open after both arms:** count the third-matrix split for it by hand
  (A_(h_2) up to the stabiliser of A_u and A_(h_1)) before any longer run.
- **A split (o000_c001 or o000_c002) with 1 to 30 open (SKIPPED included):** re-run them with 5
  minutes of CaDiCaL then 5 of XOR. **More than 30:** a 60 s pass first, then the same.
- Next (B5) d = 3 splits after this: o002_c001 (1908), o020_c000 (1666), then the three d = 2
  classes (o004_c001, o005_c005, o006_c000) after a hand count of their second-matrix split.
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

## Observations written down before the run (not graded)

- The open a031 of o000_c000 has A_(h_1) = 262144 (e_4 -> e_2), the same map as the open a083 of
  o032_c000, as o001_c000's a085 and o002_c000's a085 (both closed in m60a, 148 s and 121 s), and as
  the open kind-L instance a031 of (B6) (job m61a). o000_c000 has the same A_u (266304) as (B6)'s
  kind-L class, and its open a031 and a155 carry the same instance numbers as two of kind L's seven
  open ones. A pairing to watch, not a reduction: p = 5 against p = 6.
- 13 of the 14 open are of rank 0 on X_1, as in every split so far (a48.md to a50.md).

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
