# Job cert1: predictions, written 2026-10-22 ~14:20Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Every UNSAT answer behind Propositions 33 to 35 and Corollaries 99 to 115 is a solver answer saved
without a proof certificate. Job cert1 (cube_groups/cert1.py) is a first pilot of certificates:
it rebuilds a sample of the split instances of r3b_t7_B6_o005_c003 (Corollary 115, notes/a76.md)
with the same code that ran them, solves each with a standalone CaDiCaL (tag rel-2.2.1, built from
source) that writes a DRAT proof, and checks each proof with drat-trim (built from its source).
A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

The sample, fixed here: k = 0, 20, 40, ..., 1960 in m66's order (99 of the class's 1961 split
instances). Three of them were hard: a0060 (rank 1, UNKNOWN at 10.01 s in m88a-v2, UNSAT in
27.09 s in m90a), a0240 (rank 0, 65.84 s in m90a) and a1960 (rank 0, 56.30 s in m90b). The others
closed at 10 to 20 s budgets in m88a-v2 (class median 1.02 s). Caps: CaDiCaL 400 s, drat-trim
1200 s per instance; no instance starts after 120 minutes (those left are SKIPPED).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. Both programs build and run. Controls: the pigeonhole formula PHP(6, 5) is UNSAT in CaDiCaL and
   its proof VERIFIED by drat-trim; the same formula with an empty proof is not VERIFIED; PHP(5, 5)
   is SAT with a model that satisfies every clause.
2. The class against m66's run (m90's gate: d = 2, |G| = 512, |Adm| = 176126, orbits 135, 944,
   882 by rank on X_1) and its 1961 roots recomputed.
3. The sample: 99 instances, Lemma 93 (b) on exactly those of rank 0, and the three re-runs equal to
   m90's rows (index, map, rank, orbit size).
4. Hints 79 and units 70 on the first of rank 0, units 49 on the first of another rank; the first
   instance written as DIMACS and read back unchanged.

## Exploratory, with the decision rules

- **All 99 UNSAT in the standalone CaDiCaL within 400 s: about 95%.** (Same CNF as before, a
  different CaDiCaL version and no Python binding.)
- **All 99 proofs VERIFIED by drat-trim: about 85%.**
- **Median CaDiCaL time of the VERIFIED ones at most 3 s: about 80%.**
- **Total drat-trim time at most 3 times the total CaDiCaL time: about 50%.**
- **The largest proof is one of the three re-runs: about 70%.**

Rules:

- **All 99 VERIFIED within 60 minutes in all:** certify the whole class (the other 1862 instances)
  in jobs split by m66 order, then the other classes of (B6) in turn, smallest first. Write each
  up as certified only for what drat-trim checked.
- **Some UNSAT not VERIFIED:** no claim changes (those stay solver answers, as before); look at the
  instance and drat-trim's output before any new job (binary proofs, another CaDiCaL version).
- **Some SAT:** a contradiction with the earlier UNSAT answers, so a bug somewhere: verify the
  model as m57.py does and re-check by an independent brute force before any claim.
- **Time runs out:** certify the rest later in smaller jobs; the times say how to size them.

No speed-up is claimed. Proofs are checked and then deleted (too large to keep); the SHA-256 of
every CNF is recorded, and anyone can rebuild the CNF and the proof with the code in this folder.
