# Job m102: predictions, written 2026-10-24 in the run that started at 16:17Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m101 came back (notes/a94.md). Every graded check held (16 of 16 in each half), and all eight
positive controls were SAT with verified models, the four "relax_n" ones included (anisotropy kept
on N). But all 68 sweeps were UNKNOWN at 180 s. Its decision rule for fewer than 5 UNSAT: split the
rank-0 case by the commuting space T(N) of Lemma 104. a94.md sets the split up (Lemma 106) and
counts the spaces by hand (Lemma 107).

Job m102 (cube_groups/m102.py, two jobs as m101: m102a for pair orbits 0 to 8, 31 classes; m102b
for pair orbits 9 to 12, 37 classes). Per class, Kbar is the group of maps g_Q of Q = X / X_1 that
come from some g in GL_8(F_2) with g e_0 = e_0, g P = P, g X_1 = X_1 and g A_u = A_u g. Each g is
found in the solution space of these linear conditions, and every g found is checked again outside
that search. The instances are m101's sweep instance (unchanged, as a prefix) plus every A_n with n
in N fixed by the case:

    t1   T_(v_2) = T_(v_3) = 0          one instance per class
    t2   T_(v_2) = 0, T_(v_3) = M       one per orbit of Kbar on the 255 spaces span(I, M)
    t3   T_(v_2) = M_1, T_(v_3) = M_2   one per orbit of Kbar on the 183 commutative 3-dim algebras

Every w != 0 in N_0 adds "C_w in X_1" and, unless A_u is idempotent, "x0 not in C_w" (Lemma 105).
The parts are: check; control (60 s each); the t1 sweep of every class of the half (120 s each); a
pilot of every t3 and t2 orbit representative of one class (o000_c000 in m102a, o011_c000 in
m102b), 45 s each, stopping after 40 minutes; grade.

## Graded (each must hold)

- Unit tests pass (6 in test_m101, 7 in test_m102). One of them reads job m101's relax_n model
  of o000_c000 with v_2 replaced by v_2 + v_3 and checks that it passes every condition of the t2
  case with M = J (the all-ones matrix) outside the encoder.
- check, in each half: |GL_3(F_2)| = 168; 255 spaces span(I, M) and 183 commuting 3-dim spaces
  containing I, each 3-dim one closed under products; GL_3-orbit sizes 21, 24, 28, 42, 56, 84 (dim 2)
  and 7, 7, 8, 21, 28, 28, 84 (dim 3), the hand counts of Lemma 107; for every class: the identity
  in Kbar, every g found passes the direct check, Kbar closed under products, the orbits cover all
  255 + 183 spaces, A_u-bar I pi = A_u; m101's sweep CNF an unchanged prefix (SHA-256); 128 fixed
  map entries in every case, and 60 / 30 / 0 "in X_1" units and 70 / 23 / 0 case-two generators for
  t1 / t2 / t3.
- grade, in each half: every class has its t1 row, no ERROR, every SAT answer passes its check
  outside the encoder ((*) on all 2^11 x 2^11 pairs, normal form, sweep, the fixed maps, every C_w in
  X_1, x0 not in C_w where required, anisotropy or anisotropy on N). In m102a: the t2 control with
  M = J and anisotropy on N is SAT (the model above shows it is satisfiable).

## Exploratory

- |Kbar| = 6 for o000_c000 (by hand: g fixes e_0 and keeps R n P = span(e_1, e_2), so g_Q runs
  over a copy of GL_2(F_2)): about 70%.
- Total instances over all 68 classes (t1 + orbit representatives) at least 3,000: about 75%.
  Below 1,000: about 10%.
- Controls: the t1 "relax" ones SAT (all four): about 95%. The m102b relax_n t3 control SAT within
  60 s: about 40%.
- **t1 sweep: at least one of the 68 UNSAT: about 45%. All 68: about 10%. Any SAT: about 1%.**
- Pilot: at least one representative decided (UNSAT) within 45 s: about 50%. At least 80% of the
  pilot representatives that ran decided: about 20%. Any SAT: about 1%.
- Peak memory at most 2 GB in both: about 90%. Both finish within 150 minutes: about 85%.

## Decision rules

- **A check fails:** nothing in that half counts until it is explained.
- **A sweep or pilot SAT answer that passes every check:** an anisotropic system with t = 8 and
  dim V = 11, so A(8) = 11. Before saying so, re-check it by brute force in a separate job and
  against Lemmas 102 to 106.
- **All 68 t1 instances UNSAT:** the case dim T(N) = 1 of the rank-0 case of (B7)_8 is closed
  (given Lemmas 103 to 106). Certify with DRAT proofs before counting it in a headline.
- **At least 80% of the pilot representatives that ran decided UNSAT within 45 s:** queue the full
  split (every orbit representative of every class) in shards of at most 150 minutes, if the total
  instance count times the pilot's mean time is at most 40 job-hours. Otherwise no full split.
- **Fewer than 20% of the pilot decided and fewer than 5 t1 UNSAT:** fixing every map on N does not
  make the rank-0 instances easy at these budgets. No larger budget without a new reason. Next is
  hand work on the t2 and t3 cases (Lemma 105 (e) and the identity
  pi A_h sigma(n) = (T_n + pi A_u-bar T_n^2) pi phi(h)), or a turn to (B6)_8.
- **A relax control UNSAT, or the known t2 control not SAT:** the added conditions contradict a
  satisfiable base instance. Find the error before anything counts.
