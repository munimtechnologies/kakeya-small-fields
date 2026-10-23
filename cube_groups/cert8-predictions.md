# Job cert8: predictions, written 2026-10-23 in the run that started at 18:07Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert6 certified the 49 instances that job m86 re-ran (notes/a85.md): all VERIFIED by drat-trim.
Job m83's 53 are a family of 5-minute re-runs with the same row format, which closed the (B6)
classes o009_c005, o009_c006, o010_c003 and o010_c005 (Corollaries 102 to 105, notes/a70.md):
UNSAT in CaDiCaL through python-sat, saved without certificates. 51 are of rank 0 on X_1, with
Lemma 93 (b); in o009_c006, a0003 is of rank 1 and a3209 of rank 2.

    m83a (group a): the 11 of o009_c005 (18.37 to 51.37 s, sum 366.81 s) and the 15 of o010_c003
      (28.31 to 118.37 s, sum 701.63 s), sum 1068.44 s
    m83b (group b): the 16 of o009_c006 (0.92 to 52.93 s, sum 482.59 s; a0003 8.74 s, a3209 0.92 s)
      and the 11 of o010_c005 (28.21 to 60.53 s, sum 463.70 s), sum 946.29 s

(The times are m83a's and m83b's solve logs, logs/run-03-python.stdout.txt, the first 26 and 27
lines; every one of the 53 closed in the CaDiCaL arm, none needed the XOR arm.)

Job cert8 (cube_groups/cert8.py) certifies them with cert1's tools and certify_one, unchanged, in
m83's two groups: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks it.
Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED). Job cert7 (m85's 24) is filed in the same run with its own predictions.

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: over the eight groups of cert3 to cert6, standalone CaDiCaL took 0.60 to 1.43 times
python-sat's total, and drat-trim 0.94 to 1.08 times CaDiCaL's. At those rates group a's certify
step would take about 21 to 55 minutes and group b's 19 to 49. No speed-up or slow-down is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (each class of the group): the class against m66's run (m83's gate) and every
   root recomputed, with m83's seed (83), in m83's order (o009_c005 before o010_c003 in group a,
   o009_c006 before o010_c005 in group b).
3. groups: the two groups are m83's, 26 and 27 rows over its four classes, each (class, root) once,
   11 + 15 and 16 + 11 by class as m81a, m81b, m82a and m82b left them open, rank counts as m83
   records (group b: 25 of rank 0, one of rank 1, one of rank 2).
4. group: the group's instances, once each, named as in m83, each equal to its m83 row (m66 index,
   orbit size, A_(v_1), rank), Lemma 93 (b) on every one of rank 0 and on no other.
5. m83_probe_l (both groups): the variables, clauses, hints and units of the first rank-0 instance
   equal to m83's own check (48587, 286239, 79, 70); m83_probe_s (group b): the same for a0003
   (48587, 286218, 79, 49). So the CNFs are the ones m83 solved.

So 17 graded checks in cert8a and 18 in cert8b.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 93%.**
- **Each group's certify step at most 75 minutes: about 85%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 90%.**
- **Standalone CaDiCaL's total between 0.55 and 1.5 times m83's python-sat total in each group:
  about 75%.**
- **The two instances of rank 1 and 2 (a0003, a3209) each under 30 s of CaDiCaL: about 85%.**
- **The slowest instance in group a by CaDiCaL alone is o010_c003 a1177 (118.37 s in m83a; the next
  is 78.48 s): about 50%.**
- **Largest proof at most 500 MB: about 85%.**

Rules:

- **Both groups all VERIFIED:** the 53 instances that closed o009_c005, o009_c006, o010_c003 and
  o010_c005 after the split carry checked DRAT proofs; with cert7 (if it too is all VERIFIED) 297
  of the 495 re-runs are certified. Next: the other re-run families, one job per family.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert8_<name>.json before any new job.
- **Some SAT:** a contradiction with m83's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 102 to 105, and
  with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
