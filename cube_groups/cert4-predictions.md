# Job cert4: predictions, written 2026-10-23 in the run that started at 08:43Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert3 certified the 45 instances that job m92 re-ran (notes/a81.md): all VERIFIED by drat-trim.
The 5-minute re-runs are the hardest instances behind Theorem 33, and the next largest family of
them is job m89's 49, which closed the (B6) classes o003_c001 and o005_c001 (Corollaries 113 and
114, notes/a74.md): UNSAT in CaDiCaL through python-sat in 11.40 to 94.61 s each (sums 831.12 s in
m89a, 964.65 s in m89b), saved without certificates. Job cert4 (cube_groups/cert4.py) certifies
them with cert1's tools and certify_one, unchanged, in m89's two groups: a standalone CaDiCaL
(rel-2.2.1) writes a DRAT proof, and drat-trim checks it. Caps as in cert1: CaDiCaL 400 s,
drat-trim 1200 s per instance, no instance starts after 120 minutes (SKIPPED).

    cert4a: m89's group a, 16 of o003_c001 and 9 of o005_c001 (a0042 of rank 1); m89a's sum 831.12 s
    cert4b: m89's group b, 16 of o003_c001 and 8 of o005_c001 (all rank 0); m89b's sum 964.65 s

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: in cert3, standalone CaDiCaL took 0.93 and 0.60 times python-sat's time over the two groups,
and drat-trim 1.08 and 1.11 times CaDiCaL's. At those rates each group's certify step would take
about 17 to 30 minutes. No speed-up or slow-down is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (both classes): each class against m66's run (m89's gate) and every root
   recomputed, with m89's seed, in m89's order.
3. groups: the two groups are m89's, with its 25 and 24 rows over its two classes; m89's list check
   holds.
4. group: the group's instances, once each, named as in m89, each equal to its m89 row (m66 index,
   orbit size, A_(v_1), rank), 16 + 9 or 16 + 8 by class, Lemma 93 (b) on exactly those of rank 0.
5. m89_probe: the variables, clauses, hints and units of the first rank-0 instance (and, in cert4a,
   the rank-1 instance a0042 of o005_c001) equal to m89's own check, so the CNFs are the ones m89
   solved.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 90%.** (So far 2105 of
  2105 certificate runs VERIFIED in cert1 to cert3, 2006 distinct instances.)
- **Each group's certify step at most 45 minutes: about 80%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 85%.**
- **Standalone CaDiCaL's total at most m89's python-sat total in each group: about 65%.**
- **Largest proof at most 500 MB: about 85%.** (cert3's largest: 276 MB.)

Rules:

- **Both groups all VERIFIED:** the 49 instances that closed o003_c001 and o005_c001 after the
  split carry checked DRAT proofs, and 126 of the 495 re-runs are certified (m90's 32 inside
  cert2's whole class, m92's 45 in cert3, m89's 49 here). Next: the other re-run families,
  one job per family, then whole classes when the queue is idle.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert4_<name>.json before any new job.
- **Some SAT:** a contradiction with m89's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 113 and 114, and
  with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
