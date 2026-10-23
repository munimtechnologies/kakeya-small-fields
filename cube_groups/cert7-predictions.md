# Job cert7: predictions, written 2026-10-23 in the run that started at 18:07Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert6 certified the 49 instances that job m86 re-ran (notes/a85.md): all VERIFIED by drat-trim.
The next family of 5-minute re-runs with the same row format is job m85's 24, which closed the
(B6) classes o010_c004 and o010_c006 (Corollaries 106 and 107, notes/a71.md and a72.md): UNSAT in
CaDiCaL through python-sat, saved without certificates. All 24 are of rank 0 on X_1, with
Lemma 93 (b).

    m85a (group a): the 12 of o010_c004, 19.43 to 71.20 s each, sum 583.33 s
    m85b (group b): the 12 of o010_c006, 29.96 to 120.16 s each, sum 697.48 s

(The times are m85a's and m85b's solve logs, logs/run-03-python.stdout.txt, the first 12 lines of
each; every one of the 24 closed in the CaDiCaL arm, none needed the XOR arm.)

Job cert7 (cube_groups/cert7.py) certifies them with cert1's tools and certify_one, unchanged, in
m85's two groups: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks it.
Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED). Job cert8 (m83's 53) is filed in the same run with its own predictions.

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: over the eight groups of cert3 to cert6, standalone CaDiCaL took 0.60 to 1.43 times
python-sat's total (cert6: 1.43 and 0.80), and drat-trim 0.94 to 1.08 times CaDiCaL's. At those
rates each group's certify step would take about 12 to 35 minutes. No speed-up or slow-down is
claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (the class of the group): the class against m66's run (m85's gate) and every
   root recomputed, with m85's seed (85).
3. groups: the two groups are m85's, 12 and 12 rows over its two classes, each (class, root) once,
   12 + 12 by class as m83a and m83b left them open, rank counts as m85 records.
4. group: the group's instances, once each, named as in m85, each equal to its m85 row (m66 index,
   orbit size, A_(v_1), rank), all of rank 0, Lemma 93 (b) on every one.
5. m85_probe_l: the variables, clauses, hints and units of the first instance equal to m85's own
   check (48587, 286239, 79, 70), so the CNFs are the ones m85 solved.

So 15 graded checks in each of cert7a and cert7b.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 94%.** (So far 2248 of
  2248 certificate runs VERIFIED in cert1 to cert6, 2149 distinct instances.)
- **Each group's certify step at most 40 minutes: about 80%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 90%.**
- **Standalone CaDiCaL's total between 0.55 and 1.5 times m85's python-sat total in each group:
  about 75%.** (The range seen so far is 0.60 to 1.43; cert6's band, 0.6 to 1.3, missed in group a
  at 1.43.)
- **The slowest instance in group b by CaDiCaL alone is one of m85b's two slowest (a1593, 120.16 s,
  or a0904, 115.88 s): about 45%.** (cert6's guess of this kind missed.)
- **Largest proof at most 500 MB: about 85%.** (Largest so far: 330 MB.)

Rules:

- **Both groups all VERIFIED:** the 24 instances that closed o010_c004 and o010_c006 after the split
  carry checked DRAT proofs, and with cert8 (if it too is all VERIFIED) 297 of the 495 re-runs are
  certified. Next: the other re-run families (m82, m80r, m73, m72, m71, m70), one job per family.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert7_<name>.json before any new job.
- **Some SAT:** a contradiction with m85's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 106 and 107, and
  with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
