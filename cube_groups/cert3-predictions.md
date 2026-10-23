# Job cert3: predictions, written 2026-10-23 in the run that started at 01:32Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m92 found the last 45 open split instances of (B6) UNSAT (notes/a80.md), which gives Theorem 33
(A(7) <= 8, computer-assisted). Those 45 are among the hardest instances of the chain (14.51 to
94.22 s each in CaDiCaL through python-sat, where an ordinary split instance takes about 1 s), and
none has a certificate. Job cert3 (cube_groups/cert3.py) certifies them with cert1's tools and
certify_one, unchanged: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks
it. Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED).

    cert3a: the 25 of r3b_t7_B6_o003_c000 (all rank 0, with Lemma 93 (b)); m92a's sum 1256.38 s
    cert3b: the 20 of r3b_t7_B6_o005_c000 (18 rank 0, 2 rank 1); m92b's sum 975.46 s

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: in cert2b the 15 hard instances took drat-trim 0.93 times CaDiCaL's time in all, so at
m92's times about 45 minutes for cert3a and 35 for cert3b. A different CaDiCaL version and proof
logging can change the times either way; no speed-up or slow-down is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class, class_reps: the group's class against m66's run (m92's gate) and every root recomputed.
3. groups: the two groups are m92's two classes with its 25 and 20 rows; m92's list check holds.
4. group: the group's instances, once each, named as in m92, each equal to its m92 row (m66 index,
   orbit size, A_(v_1), rank), Lemma 93 (b) on exactly those of rank 0.
5. m92_probe: the variables, clauses, hints and units of the first rank-0 instance (and, in cert3b,
   the first rank-1 instance) equal to m92's own check, so the CNFs are the ones m92 solved.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 85%.**
- **Each group's certify step at most 90 minutes: about 75%.**
- **Every CaDiCaL run within its 400 s cap: about 90%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 70%.**
- **Standalone CaDiCaL's median within a factor of 2 of m92's (45.56 s and 49.78 s) in each group:
  about 60%.**
- **Largest proof at most 1 GB: about 80%.**

Rules:

- **Both groups all VERIFIED:** the 45 instances that closed (B6) carry checked DRAT proofs; Theorem
  33 still rests on uncertified answers elsewhere. Next: certify the 450 earlier 5-minute re-runs
  of (B5) and (B6), in groups of at most about 60, then whole classes when the queue is idle.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert3_<name>.json before any new job.
- **Some SAT:** a contradiction with m92's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Theorem 33 is then withdrawn
  until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
