# Job m104: predictions, written 2026-10-24 in the run that started at 22:09Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m103a and m103b came back (notes/a96.md). Every graded check held (14 + 14, unit tests 5 + 5)
and all six positive controls were SAT with verified models. In the three classes of the rank-0
case of (B7)_8 with d = 3, every case whose commuting space T(N) leaves k <= 4 subspaces of
Q = X / X_1 invariant was UNSAT: 57 of 57, counting job m102's pilot (21 + 16 in o000_c000, 6 in
o001_c000, 14 in o002_c000). By m103's decision rules these 57 are certified with DRAT before they
are counted, and the k <= 4 cases of all 68 classes are counted.

Job m104 (cube_groups/m104.py; three jobs, m104a, m104b and m104c) imports m102.py and m103.py
unchanged and rebuilds every CNF with m102's encoder.

    check     the 57 cases from m102.class_cases and m103.describe; each one answered UNSAT by job
              m102 or m103a; 37 / 6 / 14 by class; 19 per shard; the two programs built
    controls  cert1's three tool controls, in each job
    cert      19 cases per job: m102's sweep CNF as DIMACS, CaDiCaL 2.2.1 with an ASCII DRAT proof
              (cap 600 s), drat-trim on it (cap 1500 s), the proof deleted after the check
    count     (m104a) every case of all 68 classes typed by k: the k <= 4 cases by class and by d
    core      (m104c) six cases of six different types with k <= 4, each solved with no anisotropy
              clauses except on a subspace W of V, at three levels (100 s each): "out3"
              W = N + span(h_5, h_6, h_7), the h with pi phi(h) != 0 (dim 7, 127 vectors);
              "out3_in1" that plus h_1 (dim 8); "in4" W = N + span(h_1, ..., h_4) (dim 8). A positive
              control first: o000_c000, t2 with M = J, W = N (job m102's relax_n control). The
              CNF keeps every other condition of the case (hints, sweep, A_(v_1) = 0, Lemma 105's
              conditions, the maps T_n), so an UNSAT here uses those hand-derived conditions too.

## Graded (each must hold)

- Unit tests pass (5 in test_m104) in each job.
- check: 57 distinct cases, every one in the UNSAT answers of m102 or m103a, 37 / 6 / 14 by class,
  19 in the job's shard, both programs present; m104c also: the h with pi phi(h) != 0 are
  h_5, h_6, h_7 (indices 8, 9, 10), six distinct types with k <= 4 in the core list, and W has
  15, 127, 255 and 255 non-zero vectors at the four levels.
- controls: PHP(6, 5) VERIFIED, the empty proof rejected, PHP(5, 5) SAT with a checked model.
- cert: every case that ran is VERIFIED, and its CNF has the clause count job m103a reported for its
  class and kind (907089 / 906081 for o000_c000 and o001_c000, 907113 / 906105 for o002_c000).
- count (m104a): 68 classes; 16,272 instances; the |Kbar| distribution of notes/a95.md (1: 19,
  2: 22, 3: 5, 4: 6, 6: 6, 7: 2, 8: 4, 24: 2, 168: 2); every class with |Kbar| = 1 has exactly
  179 cases with k <= 4 (by hand: 24 + 42 + 56 spaces span(I, M) and 8 + 28 + 21 algebras); the
  k <= 4 counts of the seven classes job m103 ran (37, 6, 14, 37, 37, 30, 6); 57 with d = 3.
- core (m104c): the control SAT with a verified model; every SAT answer verified outside the
  encoder (including anisotropy on all of W); no ERROR.

## Exploratory

- All 57 VERIFIED, none skipped: about 55%. At least 50 VERIFIED: about 80%. Any SAT: about 1%.
- The largest proof at least 500 MB: about 50%. The median CaDiCaL time at most twice job m103's
  solver time for the same case: about 50%.
- count: k <= 4 cases over all 68 classes between 6,000 and 7,400: about 70% (by hand: about 6,600,
  from 179 / |Kbar| per class). Times 60 s more than 40 job-hours: about 97%. The d = 2 classes have
  between 900 and 2,000 k <= 4 cases: about 60%.
- core: at least one of the six UNSAT at "out3" within 100 s: about 35%; at least one UNSAT at
  "in4": about 30%; all six SAT at "out3": about 40%.
- Peak memory at most 3 GB in all three: about 85%. Each finishes within 170 minutes: about 85%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **CaDiCaL answers SAT for a case:** the model is checked outside the encoder in the job. If it
  passes, it is an anisotropic system with t = 8 and dim V = 11 (A(8) = 11): re-check it by brute
  force in a separate job before saying so. If it fails, the encoder or a solver is wrong: stop and
  find out which before any further claim.
- **NOT_VERIFIED:** that case is not certified; re-run it alone with a binary proof.
  **DRAT_STOPPED, UNKNOWN or SKIPPED:** re-file only those cases, with a larger cap.
- **All 57 VERIFIED:** Proposition 38 (computer-assisted): in the rank-0 case of (B7)_8, a system
  whose pair orbit has d = 3 has k(T(N)) >= 6. Write it up with its limits; it closes no class.
- **count:** if all k <= 4 cases times 60 s fit in 40 job-hours, queue them in shards of at most
  150 minutes. Otherwise, if the k <= 4 cases of the 13 d = 2 classes times 45 s fit in 20
  job-hours, queue those (at most four shards per run), to test whether the pattern holds in every
  d = 2 class. Otherwise queue nothing more from this pattern; hand work next.
- **core:** a case UNSAT at "out3" needs anisotropy only on N and on the seven cosets h + N with
  h in span(h_5, h_6, h_7) (with the hand conditions): try that case by hand first, with Lemma 109.
  No case UNSAT at any level: the refutations use anisotropy on vectors outside both W, so no small
  hand argument on those cosets alone can work.
