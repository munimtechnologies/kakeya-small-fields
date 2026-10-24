# Job m103: predictions, written 2026-10-24 in the run that started at 19:38Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m102 came back (notes/a95.md). Every graded check held (18 + 17), all six positive controls were
SAT with verified models, and all 68 t1 instances were UNKNOWN at 120 s. The pilot decided 30 of
the 68 cases of o000_c000 that it ran (d = 3) within 45 s, and 1 of 54 of o011_c000 (d = 0). Read by
hand (a95.md, Lemma 108), the o000_c000 pilot splits by the number k of subspaces of Q = X / X_1
that T(N) leaves invariant: k <= 4, 21 of 21 UNSAT; k = 6, 9 of 30; k >= 8, 0 of 17.

Job m103 (cube_groups/m103.py; two jobs, m103a and m103b) checks that reading by machine and tests
it on cases that have not run. It imports m102.py unchanged and runs every case through m102's
encoder and solver (m102.solve_one).

    check    the 16 subspaces of F_2^3; type and k for all 255 + 183 spaces against Lemma 108;
             k and type for every case of m102's two pilots, with m102's statuses
    control  m102's positive controls of the shard, again (60 s each)
    m103a    d3: every t2 / t3 case of o001_c000 (|Kbar| = 168, 13 cases) and o002_c000
             (|Kbar| = 24, 37 cases), 60 s each; rest: the 27 t2 cases of o000_c000 that m102's
             pilot skipped, 45 s; deep: four cases of o000_c000 with k = 8 or 10 (t3 F_2^3 x 2,
             t2 projection, t2 rank-1 nilpotent), 300 s
    m103b    low: every case of o011_c005 (d = 0, A_u idempotent, |Kbar| = 168) and the cases
             with k <= 4 of o004_c000 (d = 2) and o007_c008 (d = 1), 60 s; o011: the cases with
             k <= 4 of o011_c000, 120 s

## Graded (each must hold)

- Unit tests pass (5 in test_m103).
- check: 16 subspaces (1, 7, 7, 1 of dimension 0 to 3); every 2-dim space has the k of Lemma 108
  for its type (nil1 8, irr 2, proj 10, nil3 4, x(x^2+x+1) 4, x^2(x+1) 6); every 3-dim one too
  (F_8 2, F_2 x F_4 4, F_2^3 8, F_2 x F_2[x]/(x^2) 6, F_2[x]/(x^3) 4, radical square zero with a
  shared image 6, with a shared kernel 6), with type counts 8, 28, 28, 84, 21, 7, 7 equal to the
  GL_3-orbit sizes; span(I) has k = 16; every pilot label of m102 is a case of its class.
- **check, the hand reading of m102 (a95.md):** in o000_c000 every case with k <= 4 was UNSAT and
  every case with k >= 8 was UNKNOWN.
- grade: no ERROR; every control SAT and verified; every SAT answer passes its check outside the
  encoder.

## Exploratory

- rest (o000_c000): every case with k <= 4 UNSAT within 45 s: about 75%. No case with k >= 8 UNSAT:
  about 80%.
- d3: every case with k <= 4 UNSAT within 60 s, in o001_c000: about 65%; in o002_c000: about 65%.
  At least one case with k = 6 UNSAT across the two: about 70%. All 13 t2/t3 cases of o001_c000
  UNSAT: about 15%.
- deep: at least one of the four decided at 300 s: about 30%.
- low: at least 80% of the k <= 4 cases UNSAT within 60 s, in o004_c000 (d = 2): about 40%; in
  o007_c008 (d = 1): about 25%. At least one UNSAT in o011_c005: about 30%.
- o011: at least one more UNSAT among its k <= 4 cases at 120 s (m102 had 1 at 45 s): about 50%.
- Any SAT outside the controls: about 1%.
- Peak memory at most 2 GB in both: about 90%. Both finish within 150 minutes: about 85%.

## Decision rules

- **A graded check fails:** nothing in that half counts until it is explained. If the hand
  reading of m102 fails, a95.md's observation is withdrawn and corrected.
- **A SAT answer outside the controls that passes every check:** an anisotropic system with t = 8
  and dim V = 11, so A(8) = 11. Re-check it by brute force in a separate job first.
- **Every k <= 4 case of all three d = 3 classes UNSAT:** queue DRAT certificates for them (one
  job), and write up "the k <= 4 cases of the d = 3 classes are empty" only once certified. The
  d = 3 classes then come down to t1 and the k >= 6 cases: hand work on why invariant subspaces
  matter, before any bigger budget.
- **At least 80% of the k <= 4 cases UNSAT in o004_c000 and in o007_c008:** count the k <= 4 cases
  of all 68 classes; if the count times 60 s is at most 40 job-hours, queue them in shards of at
  most 150 minutes.
- **Fewer than 50% of the k <= 4 cases UNSAT in both d <= 2 classes:** the pattern belongs to
  d = 3; at d <= 2 the solver needs more than T(N). Next: a hand lemma tying an invariant subspace
  to the system (for example the span of pi beta(n, h)), not a bigger budget.
- **deep decides at least 2 of 4:** the k >= 8 cases are slow, not stuck; price a 300 s run of all
  k >= 6 cases of the d = 3 classes (at most 40 job-hours) before queuing.
