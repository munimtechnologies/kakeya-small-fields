# Job cert9: predictions, written 2026-10-23 in the run that started at 20:06Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs cert7 and cert8 certified the 77 instances that jobs m85 and m83 re-ran (notes/a86.md): all
VERIFIED by drat-trim. The next family of 5-minute re-runs is job m82's 42, which closed the (B6)
classes o008_c000, o008_c001 and o008_c003 (Corollaries 99 to 101, notes/a69.md): UNSAT in
CaDiCaL through python-sat, saved without certificates. 40 are of rank 0 on X_1, with Lemma 93 (b);
in o008_c000, a0619 and a0658 are of rank 1.

    m82a (group a): the 21 of o008_c000, 1.17 to 59.95 s each, sum 595.93 s (a0619 and a0658
      1.17 s each)
    m82b (group b): the 7 of o008_c001 (23.84 to 52.34 s, sum 265.86 s) and the 14 of o008_c003
      (20.88 to 89.20 s, sum 636.54 s), sum 902.40 s

(The times are m82a's and m82b's solve logs, logs/run-03-python.stdout.txt, the first 21 lines of
each; every one of the 42 closed in the CaDiCaL arm, none needed the XOR arm.)

Job cert9 (cube_groups/cert9.py) certifies them with cert1's tools and certify_one, unchanged, in
m82's two groups: a standalone CaDiCaL (rel-2.2.1) writes a DRAT proof, and drat-trim checks it.
Caps as in cert1: CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120
minutes (SKIPPED).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing: over the twelve groups of cert3 to cert8, standalone CaDiCaL took 0.60 to 1.43 times
python-sat's total, and drat-trim 0.94 to 1.11 times CaDiCaL's. At those rates group a's certify
step would take about 12 to 35 minutes and group b's 18 to 53. No speed-up or slow-down is claimed.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); o005_c003 against
   m66's run and its roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. class_, class_reps_ (each class of the group): the class against m66's run (m82's gate) and every
   root recomputed, with m82's seed (82), in m82's order (o008_c001 before o008_c003 in group b).
3. groups: the two groups are m82's, 21 and 21 rows over its three classes, each (class, root)
   once, 21 and 7 + 14 by class as m79a and m79b left them open, ranks 0 or 1, two of rank 1 in
   group a and none in group b, as m82 records.
4. group: the group's instances, once each, named as in m82, each equal to its m82 row (m66 index,
   orbit size, A_(v_1), rank), Lemma 93 (b) on every one of rank 0 and on no other.
5. m82_probe_l (both groups): the variables, clauses, hints and units of the first rank-0 instance
   equal to m82's own check (48587, 286225, 79, 70); m82_probe_s (group a): the same for a0619
   (48587, 286204, 79, 49). So the CNFs are the ones m82 solved.

So 16 graded checks in cert9a (10 + 2 + 2 + 2) and 17 in cert9b (10 + 4 + 2 + 1).

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 94%.** (So far 2325 of
  2325 certificate runs VERIFIED in cert1 to cert8, 2226 distinct instances.)
- **Each group's certify step at most 60 minutes: about 85%.**
- **Every CaDiCaL run within its 400 s cap: about 97%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 90%.**
- **Standalone CaDiCaL's total between 0.55 and 1.5 times m82's python-sat total in each group:
  about 75%.**
- **The two instances of rank 1 (a0619, a0658) each under 30 s of CaDiCaL: about 85%.**
- **Largest proof at most 500 MB: about 85%.**

(No "slowest instance" guess this time: that kind missed three times in a row.)

Rules:

- **Both groups all VERIFIED:** the 42 instances that closed o008_c000, o008_c001 and o008_c003
  after the split carry checked DRAT proofs, and 339 of the 495 re-runs are certified. Next: the
  other re-run families (m80r, m73, m72, m71, m70), one job per family, each checked first for
  re-runs that closed only in the XOR arm (a standalone CaDiCaL may not close those in 400 s).
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail
  in out/cert9_<name>.json before any new job.
- **Some SAT:** a contradiction with m82's UNSAT, so a bug somewhere: verify the model as m57.py
  does and re-check by an independent brute force before any claim. Corollaries 99 to 101, and
  with them Theorem 33, are then withdrawn until it is resolved.
- **UNKNOWN at 400 s:** no claim changes; re-run that instance alone with a longer cap.
- **Time runs out or the host stops a group:** certify the unreached ones in a smaller job.
