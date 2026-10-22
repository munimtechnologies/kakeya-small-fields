# Job cert2: predictions, written 2026-10-22 after 18:05Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job cert1 (the pilot) came back clean: 10 of 10 graded checks, all 99 sampled split instances of
r3b_t7_B6_o005_c003 UNSAT in a standalone CaDiCaL (rel-2.2.1) with every DRAT proof VERIFIED by
drat-trim, in 490 s for the 99. Under cert1-predictions.md's rule the whole class is certified next.

Job cert2 (cube_groups/cert2.py) certifies all 1961 split instances of the class, built by the same
code as before, in two jobs split by m66's order: cert2a (k = 0 to 980, 981 instances, 17 of the
32 that m88a-v2 left open) and cert2b (k = 981 to 1960, 980 instances, the other 15). The 99 of
cert1's sample are certified again and their CNF hashes compared with cert1's. Caps as in cert1:
CaDiCaL 400 s, drat-trim 1200 s per instance, no instance starts after 120 minutes (SKIPPED).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Sizing, from cert1: an ordinary instance took about 2.9 s in all (CaDiCaL + drat-trim about 1.95 s,
building and hashing about 0.9 s); the three hard ones took 17, 88 and 106 s. That suggests about
45 minutes of ordinary instances per group plus 15 to 30 minutes of hard ones.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. cert1's 10 checks: both programs built; the controls (PHP(6, 5) UNSAT with its proof VERIFIED,
   an empty proof rejected, PHP(5, 5) SAT with a model satisfying every clause); the class against
   m66's run and its 1961 roots recomputed; cert1's sample; hint and unit counts; DIMACS round trip.
2. groups: the two groups are the class's 1961 roots, in order, once each, with 17 and 15 of the
   re-runs; cert1's hash list has the 99 sampled k.
3. group: the group's instances, once each, named as before, Lemma 93 (b) on exactly those of rank
   0, and every re-run in it equal to m90's row (index, map, rank, orbit size).

## Exploratory, with the decision rules

- **Every instance of both groups UNSAT and VERIFIED, none SKIPPED: about 85%.**
- **All 99 of cert1's CNF hashes equal (50 in cert2a, 49 in cert2b): about 97%.**
- **Each group's certify step at most 90 minutes: about 70%** (at most 120, so none SKIPPED: about
  90%).
- **In each group the slowest instance (CaDiCaL + drat-trim) is one of the 32 that m88a-v2 left
  open: about 90%.**
- **Median CaDiCaL time at most 1.2 s in each group: about 75%.**
- **Slowest CaDiCaL time at most 150 s over both groups: about 75%.**
- **drat-trim's total at most 1.5 times CaDiCaL's total in each group: about 70%.**

Rules:

- **Both groups all VERIFIED:** Corollary 115 holds with every one of its 1961 CNFs certified by
  drat-trim (the first class of (B6) certified in full). Next: certify the 430 instances that needed
  5-minute re-runs across all classes (the hardest ones), then whole classes when the queue is idle.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers); read drat-trim's tail in
  out/cert2_<name>.json before any new job.
- **Some SAT:** a contradiction with the earlier UNSAT answers, so a bug somewhere: verify the model
  as m57.py does and re-check by an independent brute force before any claim.
- **A hash differs:** the instance builder is not deterministic across runs; find out why before the
  certificates are said to cover the instances that ran in m88a-v2 and m90.
- **Time runs out:** certify the SKIPPED ones in a smaller job.
