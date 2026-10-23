# Job cert5: predictions, written 2026-10-23 in the run that started at 11:12Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert4 certified the 49 instances that job m89 re-ran (notes/a82.md): all VERIFIED by drat-trim.
The next family of 5-minute re-runs with the same row format is job m87's 45, which closed the
(B6) classes o010_c001 (Corollary 116, notes/a78.md), o010_c008 and o005_c002 (Corollaries 111
and 112, notes/a73.md): UNSAT in CaDiCaL through python-sat, saved without certificates.

    m87a-v3 (group a): the 20 of o010_c001, 1.33 to 84.49 s each, sum 971.30 s
      (a0152 of rank 2: 1.33 s; the other 19 of rank 0, with Lemma 93 (b))
    m87b (group b): the 15 of o010_c008 (sum 664.89 s) and the 10 of o005_c002 (sum 373.79 s),
      all of rank 0, 24.75 to 92.79 s each, sum 1038.68 s

(m87a-v3 was stopped by its host after its 20 re-runs finished; the times are its solve log,
logs/run-03-python.stdout.txt. m87b's are its out/grade.json "rows".)

Job cert5 (cube_groups/cert5.py) certifies them with cert1's tools and certify_one, unchanged, in
m87's two groups: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks it.
Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: in cert4, standalone CaDiCaL took 1.15 and 1.18 times python-sat's total, and drat-trim
0.94 and 0.97 times CaDiCaL's; in cert3 the CaDiCaL ratios were 0.93 and 0.60. At cert4's rates
group a's certify step would take about 37 minutes and group b's about 40. No speed-up or slow-down
is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (each class of the group): the class against m66's run (m87's gate) and every
   root recomputed, with m87's seed (87), in m87's order (o010_c008 before o005_c002 in group b).
3. groups: the two groups are m87's, 20 and 25 rows over its three classes, each (class, root) once,
   20 + 15 + 10 by class as m87's earlier splits left them open, rank counts as m87 records.
4. group: the group's instances, once each, named as in m87, each equal to its m87 row (m66 index,
   orbit size, A_(v_1), rank), 19 + 1 or 25 by rank, Lemma 93 (b) on exactly those of rank 0.
5. m87_probe: the variables, clauses, hints and units of the first rank-0 instance (and, in cert5a,
   the rank-2 instance a0152) equal to m87's own check, so the CNFs are the ones m87 solved.

So 16 graded checks in cert5a and 17 in cert5b.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 92%.** (So far 2154 of
  2154 certificate runs VERIFIED in cert1 to cert4, 2055 distinct instances.)
- **Each group's certify step at most 50 minutes: about 75%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 90%.**
- **Standalone CaDiCaL's total between 0.8 and 1.4 times m87's python-sat total in each group:
  about 65%.** (cert4's guess "at most m89's total" missed in both groups, at 1.15 and 1.18; this
  one is a band, so it can miss on either side.)
- **The rank-2 instance a0152 (1.33 s in m87a-v3) under 10 s of CaDiCaL: about 85%.**
- **Largest proof at most 500 MB: about 85%.** (cert3's and cert4's largest: 276 MB and 268 MB.)

Rules:

- **Both groups all VERIFIED:** the 45 instances that closed o010_c001, o010_c008 and o005_c002
  after the split carry checked DRAT proofs, and 171 of the 495 re-runs are certified (m90's 32
  inside cert2's whole class, m92's 45 in cert3, m89's 49 in cert4, m87's 45 here). Next: the
  other re-run families, one job per family, then whole classes when the queue is idle.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert5_<name>.json before any new job.
- **Some SAT:** a contradiction with m87's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 111, 112 and 116,
  and with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
