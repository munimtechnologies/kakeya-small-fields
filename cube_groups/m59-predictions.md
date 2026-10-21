# Job m59: predictions, written 2026-10-20 ~21:00Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m59 (cube_groups/m59.py) carries out rules that jobs m57 and m58 wrote down before they ran.
The setting is in notes/a42.md, a45.md, a47.md and a48.md.

- m58's rule (m58-predictions.md), kind graph: a025 closed (UNSAT, 157 s) and batch b closed 87 of
  89, which is "1 to 10 open". The two open ones, r3g_t7_B6_o002_a117 and a153 (both rank 0 on
  X_1, UNKNOWN at 95 s), are re-run with a 15-minute cap in both arms.
- m57's rule (m57-predictions.md), kind L: a07 closed, so the kind-L class of (B6) is due.
- m57's rule, (B5) group a: 14 of 17 closed. The two open ones with d <= 2 (o009_c009 and
  o016_c024, both d = 1) go to the XOR arm, which m57b made the second pass (18 of 21). The open
  d = 3 class o001_c000 goes to the split of Proposition 32 (job m55: 445 instances).
- The playbook's order for the (B5) d = 3 splits, smallest first: o002_c000 (421) runs with
  o001_c000.

## Why the instances are the same as before

m59.py imports m57.py and m55.py unchanged. The a117 and a153 instances are m58's (graph_spec is
m58.py's, and A_(h_1) is copied from m58.py's GRAPH_B, entries 28 and 64). A kind-L instance is
m42's encoding with A_u = 266304 (e_4 -> e_2, e_5 -> e_1, e_6 -> e_0, the representative of
r3b_t7_B6_o000_c000 in job m45's list) and A_(v_1) fixed to a class representative. m52 counted
these classes in a frame of its own (x0 = e_6), so m59 counts them again in m42's coordinates
(x0 = e_0, P = span(e_1, ..., e_6)) by the method of m55.py, and runs only if the two counts
agree. A (B5) split instance is m42's encoding with m42's A_u and A_(v_1) fixed to one of m55's
representatives, which m55.py recomputes here (its orbit roots are the smallest index of each
orbit, so they do not depend on the random generators).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks; all held in m57a, m57b, m58a).
2. a117 and a153 are admissible for kind graph with rank 0 on X_1; o009_c009 and o016_c024 have
   d = 1.
3. Kind L: A_u has kernel X_1 = span(e_0, ..., e_3) and image R = span(e_0, e_1, e_2), so d = 3 and
   x0 in R. |G| = 12288 and |Adm| = 344 * 512 - 2 = 176126 (by hand: the columns at e_1, e_2, e_3
   are a triple in R of rank at most 2, 512 - 7 * 6 * 4 = 344 ways; the columns at e_4, e_5, e_6
   are free in R, 512 ways; minus 0 and A_u). 308 classes, 51 / 174 / 83 by rank on X_1, as m52.
   Every representative is admissible, of the recorded rank, and the 308 maps and their sums with
   A_u are 616 different maps.
4. (B5) splits: m55's checks for both classes (structure, |G| = 24576, |Adm| = 405566, closed
   action) and m55's counts, o002_c000 421 = 64 / 257 / 100, o001_c000 445 = 67 / 268 / 110.
   Every representative passes Proposition 32 (a) in m57's terms (kills x0, H0 into R, rank on X_1
   at most 2, rank at most 3, rank of A + A_u at most 3) and they are distinct with their sums.
5. One kind-L instance has 79 hints and 49 consistent unit clauses; one split instance 111 and 49.
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u and A_(v_1) as
   fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **a117 and a153: both UNSAT within the 15 + 15 minutes.** a025 (rank 0, the same kind) closed in
  157 s of CaDiCaL and a07 (kind P) in 291 s.
- **o009_c009 and o016_c024: at least 1 of 2 UNSAT** in 5 minutes of XOR. m57b's XOR pass closed
  18 of 21 such classes, every one in under 108 s, but these two were picked by m57a's CaDiCaL
  failure at 15 minutes, as those were.
- **Kind L: 290 to 308 of 308 UNSAT at 25 s, no SAT**, the open ones of rank 0 on X_1. Kind graph
  closed 176 of 178 at 95 s with median about 1 s, and its slow instances were of rank 0.
- **(B5) splits: 400 to 421 of 421 and 420 to 445 of 445 UNSAT at 20 s, no SAT.** No (B5) split
  has run before, so the speed is a guess from (B6); an instance with phi of rank 5 has one more
  element of ker phi than in (B6).

Rules:

- **a117 and a153 both UNSAT:** all 178 instances of kind graph are UNSAT, so the class is empty
  (computer-assisted, given Proposition 30 (a) and m42's hints); with kind P (Corollary 61), two of
  the three (B6) classes with d = 3 are empty, and (B6) goes to 16 of 68.
- **Either still open after both arms:** count the third-matrix split for it by hand (A_(h_2) up to
  the stabiliser of A_u and A_(h_1)) before any longer run.
- **Kind L all 308 UNSAT:** the kind-L class is empty, and (B6) has no class with d = 3 left.
- **Kind L 1 to 30 open:** re-run them with 5 minutes of CaDiCaL then 5 of XOR. **More than 30:**
  a 60 s pass first, then the same.
- **(B5) split class all UNSAT:** that class is empty; (B5) goes up by one per class.
- **(B5) split class with 1 to 30 open:** re-run them as for kind L. More than 30: a 60 s pass.
- **o009_c009 or o016_c024 still open after XOR:** CaDiCaL for 30 minutes alone (m48's d <= 2 rate
  at 15 minutes was 13 of 14 for d = 2, 7 of 14 for d = 1), then the second-matrix split.
- Next (B5) d = 3 splits after this: o000_c000 (671), o032_c000 (856), then the rest.
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
