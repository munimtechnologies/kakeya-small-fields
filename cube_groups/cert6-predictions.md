# Job cert6: predictions, written 2026-10-23 in the run that started at 14:27Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert5 certified the 45 instances that job m87 re-ran (notes/a84.md): all VERIFIED by drat-trim.
The next family of 5-minute re-runs with the same row format is job m86's 49, which closed the
(B6) classes o009_c007, o010_c000 and o010_c007 (Corollaries 108 to 110, notes/a72.md): UNSAT in
CaDiCaL through python-sat, saved without certificates. All 49 are of rank 0 on X_1, with
Lemma 93 (b).

    m86a (group a): the 14 of o009_c007, 13.61 to 53.49 s each, sum 444.98 s
    m86b (group b): the 22 of o010_c000 (19.19 to 129.54 s, sum 1141.13 s) and the 13 of
      o010_c007 (20.14 to 90.47 s, sum 662.20 s), sum 1803.33 s

(The times are m86a's and m86b's solve logs, logs/run-03-python.stdout.txt, the first 14 and 35
lines; every one of the 49 closed in the CaDiCaL arm, none needed the XOR arm.)

Job cert6 (cube_groups/cert6.py) certifies them with cert1's tools and certify_one, unchanged, in
m86's two groups: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks it.
Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: over the six groups of cert3 to cert5, standalone CaDiCaL took 0.60 to 1.18 times
python-sat's total (cert5: 0.68 and 1.08), and drat-trim 0.94 to 1.00 times CaDiCaL's. At those
rates group a's certify step would take 9 to 18 minutes and group b's 36 to 71. No speed-up or
slow-down is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (each class of the group): the class against m66's run (m86's gate) and every
   root recomputed, with m86's seed (86), in m86's order (o010_c000 before o010_c007 in group b).
3. groups: the two groups are m86's, 14 and 35 rows over its three classes, each (class, root) once,
   14 + 22 + 13 by class as m84a, m84b and m85a left them open, rank counts as m86 records.
4. group: the group's instances, once each, named as in m86, each equal to its m86 row (m66 index,
   orbit size, A_(v_1), rank), all of rank 0, Lemma 93 (b) on every one.
5. m86_probe_l: the variables, clauses, hints and units of the first instance equal to m86's own
   check (48587, 286239, 79, 70), so the CNFs are the ones m86 solved.

So 15 graded checks in cert6a and 17 in cert6b.

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 93%.** (So far 2199 of
  2199 certificate runs VERIFIED in cert1 to cert5, 2100 distinct instances.)
- **Group a's certify step at most 30 minutes and group b's at most 80: about 80%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 90%.**
- **Standalone CaDiCaL's total between 0.6 and 1.3 times m86's python-sat total in each group:
  about 70%.** (The band is the range seen so far, 0.60 to 1.18, with a little room above. cert5's
  band, 0.8 to 1.4, missed in group a at 0.68.)
- **The slowest instance in group b by CaDiCaL is one of m86's three slowest there (o010_c000
  a0386, a0214, or o010_c007 a0201): about 55%.**
- **Largest proof at most 500 MB: about 80%.** (cert5's largest: 330 MB, from an instance of
  139 s in standalone CaDiCaL.)

Rules:

- **Both groups all VERIFIED:** the 49 instances that closed o009_c007, o010_c000 and o010_c007
  after the split carry checked DRAT proofs, and 220 of the 495 re-runs are certified (m90's 32
  inside cert2's whole class, m92's 45 in cert3, m89's 49 in cert4, m87's 45 in cert5, m86's 49
  here). Next: the other re-run families, one job per family, then whole classes when the queue is
  idle.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert6_<name>.json before any new job.
- **Some SAT:** a contradiction with m86's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 108 to 110, and
  with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
