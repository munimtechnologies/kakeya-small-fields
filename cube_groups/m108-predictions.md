# Job m108: predictions, written 2026-10-25 in the run that started at 09:30Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m107a, b, c, e and f came back (notes/a100.md); every graded check held. The four d = 2 cases
still open were UNSAT with anisotropy on N (147 to 218 s), so all 1,115 d = 2 cases with
k(T(N)) <= 4 are UNSAT, without certificates. In all ten core and k = 6 cases the deletion-minimal
set of hand conditions is {M} alone. With no anisotropy at all, 16 of the 56 cases with k = 6 of
the d = 3 classes are UNSAT and every case with k = 8 or 10 is SAT.

Job m108 (cube_groups/m108.py; jobs m108a-d, m108g, m108h) imports m102.py to m107.py unchanged.

    m108a-d  DRAT certificates of the 1,115 d = 2 cases (279, 279, 279, 278): each from the CNF that
             was UNSAT for it (m102's sweep CNF; for the four of m107a the relax CNF with anisotropy
             on N), CaDiCaL with an ASCII DRAT proof, drat-trim, after cert1's three tool controls;
             CaDiCaL cap 900 s, drat-trim cap 1,500 s (3,000 s for the four)
    m108g    the six core cases; m108h the four k = 6 cases: the system (*) split into 16 groups,
             (L) by the kinds (u, v, h) of (i, j) and (Q) by the kinds of {i, j, k}; with the normal
             form and M kept, all 16, then a deletion-minimal set of groups with the CNF still UNSAT,
             dropping the groups with most h first (STAR_DROP); 120 s per solve, after a positive
             control. m108h then runs the "M only" CNF (all 16 groups, normal form, M) on the twelve
             other k = 6 cases that were UNSAT at "none" in m107b/c

## Graded (each must hold)

- Unit tests pass (9 in test_m108) in each job.
- m108a-d check: 1,115 distinct cases, by class equal to job m104a's count (m105.D2_LE4), all d = 2
  and k <= 4, the four of m107a and the 28 of m106a among them, this shard's size, both programs
  present. Controls: PHP(6, 5) VERIFIED, the empty proof rejected, PHP(5, 5) SAT with a checked
  model. Every case that ran is VERIFIED; within one class, kind and CNF the clause count is the
  same.
- m108g, m108h check: with all 16 groups encode_star is sat_aniso.encode clause for clause (hash,
  count, variables); the "M only" CNF is m107.build_groups(spec, case, ["M"]) clause for clause;
  the group counts are the hand counts (8, 24, 56, 24, 72, 168, 56, 168, 392; 72, 504, 504, 24,
  504, 1,512, 840); M adds 128 units; 6 items (g), 16 (h).
- m108g, m108h: no ERROR; the control SAT and verified; every SAT verified outside the encoder (the
  normal form, M, every group of (*) it kept); every item UNSAT with all 16 groups.

## Exploratory

- m108a-d: all 1,115 VERIFIED: about 75%. Nothing skipped for time: about 65%. The four "n" cases
  all VERIFIED: about 60%. Largest proof under 1 GB: about 70%. Each shard within its timeout:
  about 85%. Peak memory at most 2 GB in every shard: about 80%.
- m108g + m108h: every kept set has at most 4 of the 16 groups: about 45%. Q_hhh dropped in every
  item: about 70%. Some item keeps no group of (Q): about 20%. L_uu dropped in every item (it is
  fixed by the normal form): about 80%. Every kept set contains a group with u: about 60%. The six
  core cases all keep the same set: about 25%. Every kept group proven needed: about 60%.
- m108h "M only": at least 10 of the 12 UNSAT at 120 s: about 70%. All 12: about 50%.
- Peak memory at most 1 GB in g and h: about 90%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V** (any job): a system with t = 8 and dim V = 11
  (A(8) = 11). Re-check it by brute force in a separate job before saying anything.
- **m108a-d, all 1,115 VERIFIED:** Proposition 39: in the rank-0 case of (B7)_8, no case with
  k(T(N)) <= 4 of a class with d >= 2 is possible (with Proposition 38 for d = 3; computer-assisted,
  DRAT-certified, resting on unchecked hand lemmas). Then the d = 1 cases with k <= 4 at "n" (3,876
  cases, five shards). Some not verified or skipped: re-run only those (same rule, next version).
- **m108g/h, small kept sets (at most 4 groups) that agree by type:** the precise target of Lemma
  110 (those equations of (*), the normal form and M contradict each other for that T(N)). Write the
  lemma only if fully proved by hand; otherwise state the observation. Kept sets that differ by
  type: report by type and try the simplest first.
- **m108h, "M only" UNSAT for all 12:** "none" UNSAT and "M only" UNSAT agree on every k = 6 case
  tried; next, "M only" on all 88 cases with k > 4 of the d = 3 classes is not needed (m107b/c
  already ran "none" there); instead the hand proof is the target.
