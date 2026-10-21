# Job m61: predictions, written 2026-10-20 ~22:50Z before either group ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m61 (cube_groups/m61.py) carries out rules that jobs m58 and m59 wrote down before they ran
(m58-predictions.md, m59-predictions.md). The setting is in notes/a42.md, a47.md, a48.md and a50.md.

## What m58b and m59a found (graded 2026-10-20 ~22:40Z, all checks held, no SAT)

- m59a, kind graph: r3g_t7_B6_o002_a117 and a153 UNSAT in 151.7 s and 240.0 s of CaDiCaL. With the
  176 closed by m54a and m58a, all 178 instances are UNSAT: the kind-graph class is empty
  (Corollary 62 in a50.md). Guess (both UNSAT within 15 + 15 minutes) held.
- m59a, kind L: 301 of 308 UNSAT at 25 s; open 7, all of rank 0 on X_1, each UNKNOWN at its full
  25 s (a031, a115, a155, a160, a182, a288, a307). By rank: 0: 44 of 51, 1: 174 of 174, 2: 83 of 83.
  Guess (290 to 308) held.
- m58b, XOR pass over the 51 open (B6) classes with d <= 2: 0 of 51 UNSAT at about 176 s each
  (the shared budget gave each 176.4 s of its 180 s cap). Guess (5 to 20) missed; the shared-A_u
  guess (at least 3 of five) missed too: none of the five closed.

So m59's rule for kind L (1 to 30 open: 5 minutes of CaDiCaL, then 5 of XOR) and m58's rule for 9
or fewer (CaDiCaL for 15 minutes on the 28 classes of m47's list; the second-matrix split for the
23 of m45's list, counted by hand first) apply.

## The plan

- m61a: the 7 kind-L instances (CaDiCaL 5 minutes, then XOR 5 minutes if open), then the 7 classes
  with d = 2 of m47's list, CaDiCaL 15 minutes each, 150 minutes in all.
- m61b: the 16 classes with d = 1 of m47's list, CaDiCaL 15 minutes each, 152 minutes in all (so
  that 10 fit if every one runs to its cap).
- A class entry runs only if its whole 15 minutes fit in what is left; otherwise it is SKIPPED and
  goes to the next job unchanged. The 5 classes with d = 0 of m47's list wait for the next job.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks).
2. Kind L: A_u has kernel X_1 and image R = span(e_0, e_1, e_2), d = 3, x0 in R. The 7 maps are in
   Adm of Proposition 30 (a), of rank 0 on X_1, have the m59 index m59a recorded, and with their
   sums with A_u are 14 different maps; 7 = 308 - 301.
3. m47's list: 28 names, none closed before, none in m45's list of 23; every representative has
   kernel X_1, the image R of its pair and rank 3; d = 2 / 1 / 0 for 7 / 16 / 5, each equal to the
   hand value of its pair; no two representatives of a pair coincide.
4. One kind-L instance: 79 hints and 49 consistent unit clauses, in both arms (XOR constraints in
   the XOR arm); one class instance: 79 hints, no unit clauses for A_(v_1).
5. Any SAT at t = 7 is verified: a system, anisotropic, in the normal form with A_u (and A_(v_1))
   as fixed, rank A_u = 3 and every rank <= 4.

## Exploratory, with the decision rules

Guesses (low confidence):

- **Kind L: at least 5 of 7 UNSAT in the 5 minutes of CaDiCaL, all 7 after both arms.** The two
  rank-0 kind-graph instances that were open at 95 s closed in 152 s and 240 s, and a025 in 157 s.
- **m61a, d = 2: 1 to 4 of 7 UNSAT at 15 minutes.** In (B5), m48's 15-minute pass closed 13 of 14
  classes with d = 2, but (B6) has been harder at every step: m45's 624 s of CaDiCaL closed 5 of
  about 30 classes, and m58b's XOR pass none.
- **m61b, d = 1: 1 to 5 of the (at most 10) that run.** m48's rate for d = 1 in (B5) was 7 of 14.
- **Both groups end inside their time; m61a reaches all 7 d = 2 classes** (it does if the kind-L
  part takes at most 45 minutes).

Rules:

- **All 7 kind-L instances UNSAT:** all 308 are, so the kind-L class is empty (computer-assisted,
  given Proposition 30 (a) and m42's hints). With kind P (Corollary 61) and kind graph
  (Corollary 62), (B6) has no class with d = 3 left; (B6) goes to 17 of 68.
- **A kind-L instance still open after both arms:** count the third-matrix split for it by hand
  (A_(h_2) up to the stabiliser of A_u and A_(h_1)) before any longer run.
- **A class UNSAT:** (B6) goes up by one per class.
- **A class still open at 15 minutes:** it joins m45's 23 for the second-matrix split by d, whose
  hand count for d <= 2 (Proposition 33) is written before any job runs it.
- **SKIPPED classes and the 5 with d = 0:** the next job, unchanged, 15 minutes each.
- A verified SAT at t = 7 would be a candidate for A(7) = 9. Re-check it with an independent brute
  force before any claim.

## Observation written down before the run (not graded)

The kind-L class of (B6) and the (B5) class r3b_t7_B5_o000_c000 (in job m60b's tail) have the same
A_u = 266304. The open kind-L instance a031 has A_(h_1) = 262144 (e_4 -> e_2), the same map as the
open (B5) instances a085 of o001_c000 and o002_c000 (job m60a), whose A_u differs. Not a reduction.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
