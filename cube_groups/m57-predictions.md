# Job m57: predictions, written 2026-10-20 ~19:00Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m57 (cube_groups/m57.py) follows three rules written down before the jobs they grade had run.
The setting is in notes/a41.md, a42.md, a45.md and a46.md.

- m53's rule (m53-predictions.md): 30 to 39 of its 40 instances UNSAT with no SAT means re-running
  the open ones with a 15-minute cap. m53 closed 39 of 40. The open one is r3p_t7_B6_o001_a07
  (rank 0 on X_1, class size 56), UNKNOWN at 210 s.
- m50's rule (m50-predictions.md): if the XOR arm does not win on calibration (it did not: 4 of 9
  UNSAT, median ratio 0), CaDiCaL stays, and m48's batch c runs as staged. A target that closes
  counts as UNSAT. r3b_t7_B5_o027_c001 (d = 1) closed in 4.6 s.
- m48's plan: batch c at 15 minutes per class, as batches a and b ran.

Group a is m48c as staged. Group b re-runs a07 and makes one new, measured use of the XOR arm. m50
showed the arm is uneven but sometimes decisive where CaDiCaL is not (o027_c001 in 4.6 s after
CaDiCaL failed at 600 s; o047_c003 in 3.3 s against 175 s). Group b therefore tries it, 5 minutes
each, on the 21 open classes of (B5) with d <= 2 that CaDiCaL has already failed at 10 to 15
minutes.

## Why the instances are the same as before

m57.py copies m42.py's encode_fixed, add_hints, params and planted control unchanged, and m53.py's
fix_a1. A (B5) instance depends only on A_u. The representatives are m48.py's and m46.py's, whose
check parts (jobs m46a/b, m48a/b) matched them against m42.py's recomputed classification of (B5).
a07 is m53's instance with A_u = e_4 -> e_1, e_5 -> e_2, e_6 -> e_3 and A_(v_1) = e_4 -> e_1
(m53 out/r3p_t7_B6_o001_a07.json: au 134744064, a1 2048).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. Every one of the 38 representatives has kernel X_1 and image R of its pair and rank 3.
2. d = dim(X_1 n R), counted by hand from the pair tables: batch c has 1 / 8 / 5 / 3 classes with
   d = 3 / 2 / 1 / 0. The 21 leftovers have 0 / 4 / 14 / 3.
3. a07: A_u has kernel span(e_0, ..., e_3) and image span(e_1, e_2, e_3), so d = 3. A_(v_1) is in
   Adm of Proposition 30 (a), with rank 0 on X_1.
4. Hints: 111 for (B5) and 79 for (B6), as m42.py. 49 unit clauses for A_(v_1), with consistent
   units in both arms. The XOR instance has fewer variables than the CNF and at least one XOR
   constraint.
5. On 100 random small systems and mutations, the XOR instance accepts exactly the anisotropic
   systems, as the CNF does.
6. The planted system at t = 6 with A_(v_1) fixed to its own map: accepted in both arms (45 hints),
   rejected when one entry of A_(v_1) is flipped, and solved SAT and verified in both arms (an
   UNKNOWN there is reported, ungraded).
7. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u (and A_(v_1))
   as fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **Group a:** 10 to 15 of 17 UNSAT, no SAT. From m48a and m48b's rates at 15 minutes (d = 3: 2 of
  4; d = 2: 13 of 14; d = 1: 7 of 14; d = 0: 2 of 2), the expected number is about 13.
- **a07:** UNSAT under CaDiCaL within 15 minutes. Its five siblings with rank 0 on X_1 closed in 2
  to 43 s, so this is close to a coin toss, leaning UNSAT.
- **XOR sweep:** 2 to 7 of 21 UNSAT. These classes already resisted CaDiCaL, and the XOR arm
  decided only 4 of 9 classes that CaDiCaL decides.

Rules:

- **a07 UNSAT (either arm):** all 40 instances of the kind-P class of (B6) are UNSAT, so the class
  is empty (computer-assisted, given Proposition 30 (a) and m42's hints). (B6) moves to 15 of 68.
  The second-matrix split has then closed a d = 3 class of (B6) for the first time, so the kind-L
  class (308 instances, count confirmed by job m52) is due, after m54a's result for kind graph.
- **a07 UNKNOWN in both arms:** count the third-matrix split for a07 by hand (A_(h_2) up to the
  stabiliser of A_u and A_(h_1)) before any longer run.
- **XOR sweep, 5 or more of 21 UNSAT:** the XOR arm becomes the second pass for every class
  CaDiCaL leaves open with d <= 2. The next such job sends the open (B6) classes with d <= 2 to it,
  in batches.
- **XOR sweep, 4 or fewer:** the XOR arm is kept only for named single targets, not as a sweep.
- **Group a:** each UNSAT counts. Open classes with d <= 2 go to whichever second pass the rule
  above picks. o001_c000 (d = 3), if open, goes to the split of Proposition 32 (job m55's counts).
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
