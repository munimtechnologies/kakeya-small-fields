# Job m58: predictions, written 2026-10-20 ~20:00Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m58 (cube_groups/m58.py) carries out three rules written down before the jobs they grade had
run. The setting is in notes/a42.md, a44.md, a46.md and a47.md.

- m54's rule (m54-predictions.md): batch a closed 88 of 89 with no SAT, which is "80 to 89", so
  batch b is queued unchanged and the open instance of batch a is re-run with a 10-minute cap. The
  open one is r3g_t7_B6_o002_a025 (rank 0 on X_1, A_(h_1) = e_4 -> e_3, class size 24), UNKNOWN at
  95 s.
- m57's rule (m57-predictions.md): a07 UNSAT, so the kind-P class of (B6) is empty and the kind-L
  class is due. Kind L is not in m58: its 308 representatives need m52's frame moved to m42's
  coordinates, which no job has checked yet (see the rules below).
- m57's rule: the XOR pass closed 18 of 21 (5 or more), so the XOR arm becomes the second pass for
  open classes with d <= 2, the (B6) ones next, in batches.

Group a is m54b as staged plus a025. Group b is the XOR pass over all 51 open classes of (B6) with
d <= 2, at most 3 minutes each, in one batch: every one of m57b's 18 XOR answers came in under
108 s, so 3 minutes is the cap that would have caught all of them, and 51 x 3 minutes fits one job.

## Why the instances are the same as before

m58.py imports m57.py unchanged (m42.py's encode_fixed, add_hints and params, m53.py's fix_a1,
m50.py's XorCNF). An instance of group a is m54's: m42b's A_u for pair orbit 2 and A_(h_1) fixed
to one of the 178 representatives of Proposition 30, as m54a recorded them in m42's coordinates
(out/m54_reps.json, whose 178 entries m54a's check found admissible, distinct with their sums with
A_u, and of the rank on X_1 that m52 gave). An instance of group b is m42's: A_u fixed to the class
representative. The 23 classes from m45 were matched against m42's recomputed classification by
m45's check part; the 28 from m47's list were transcribed from m42b's recorded output, and m47's
check never ran, so m58 checks their kernels, images and ranks but not their class membership.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks; all held in m57b).
2. Kind graph: A_u has kernel X_1, image R = span(e_3, e_2, e_0 + e_1), d = 3, dim(R n P) = 2, and
   x0 = e_0 is not in R.
3. a025 and the 89 maps of batch b are admissible with the recorded rank on X_1; batch b has 16 / 64
   / 9 of rank 0 / 1 / 2 (so that, with batch a's 2 / 30 / 57, the 178 are m52's 18 / 94 / 66); the
   90 maps and their sums with A_u are 180 different maps.
4. m58's instance for m54's a088 has the size m54 recorded: 48587 variables, 286218 clauses, 79
   hints, 49 unit clauses, no contradictory units.
5. (B6): 23 + 28 = 51 names, none among the 11 classes closed earlier; every representative has
   kernel X_1, the image R of its pair and rank 3; d = 2 / 1 / 0 for 13 / 31 / 7 of them, and d
   equals the hand value of its pair; no two representatives coincide; 79 hints in both arms.
6. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u (and A_(v_1))
   as fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **Batch b: 80 to 89 of 89 UNSAT, no SAT.** Batch a closed 88 of 89 with median 0.97 s, but batch
  b holds 16 of the 18 instances with rank 0 on X_1, the slow ones (batch a: 6.5 s and UNKNOWN at
  95 s), so the open ones, if any, will be of rank 0.
- **a025: UNSAT within 10 minutes of CaDiCaL, about even odds.** Its kind-P counterpart a07 (same
  m52 index 512, rank 0) closed in 291 s.
- **Host control a085: UNSAT within 60 s** (6.5 s in m54a). Reported, not graded.
- **XOR pass on (B6): 5 to 20 of 51 UNSAT**, more of them among the 28 from m47's list (CaDiCaL
  had only about 250 s on them) than among the 23 from m45 (624 s of CaDiCaL, and m49's control).
  The guess is lower than (B5)'s 18 of 21 because in job m50 the XOR arm left both (B6) calibration
  classes undecided at 600 s and the (B6) target o008_c000 at 720 s.
- **Shared A_u.** Pair orbits 0 to 10 of (B6) and of (B5) have the same X_1 and R, and some classes
  have the same representative A_u in both (the instances differ: phi has rank 6 in (B6), 5 in
  (B5)). Five of the 51 share A_u with a (B5) class that m57b's XOR pass closed (o008_c001,
  o009_c004, o010_c002, o010_c003, o010_c007), and three with the three (B5) classes it left open
  (o004_c001; o005_c003 = (B5) o005_c005; o006_c000). Guess: at least 3 of the five close, at most
  1 of the three.

Rules:

- **a025 and all 89 of batch b UNSAT:** all 178 instances of the kind-graph class are UNSAT, so
  the class is empty (computer-assisted, given Proposition 30 (a) and m42's hints), and (B6) goes to
  16 of 68.
- **Batch b leaves 1 to 10 open, or a025 open in both arms:** re-run those with a 15-minute cap in
  both arms; if a rank-0 instance is still open after that, count the third-matrix split for it by
  hand before any longer run.
- **Batch b leaves more than 10 open:** count the third-matrix split by hand first.
- **XOR pass, 10 or more of 51 UNSAT:** the open ones go next to CaDiCaL at 15 minutes (m47's plan,
  never run) for the m47 classes, and the m45 classes go to the second-matrix split by d (the
  count of Proposition 30 carried to d <= 2 is written by hand first).
- **XOR pass, 9 or fewer:** m47's plan (CaDiCaL, 15 minutes) for the 28 m47 classes, and the
  second-matrix split for the m45 classes, as above.
- **Kind L (308 instances):** due now. The next job moves m52's kind-L representatives to m42's
  coordinates by a permutation checked as m54 checked Bm (products, identity, x0, P, X_1, R and A_u
  = 266304 sent to m42's), with m52's count 308 = 51 / 174 / 83 as the gate.
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
