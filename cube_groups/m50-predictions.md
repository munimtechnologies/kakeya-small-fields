# Job m50: CryptoMiniSat with native XOR against CaDiCaL; predictions, written 2026-10-20 ~13:20Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m50.py (Apache-2.0), which
builds m42.py's instances unchanged except for how linear conditions are handed to the solver, with
sat_aniso.py from the repository and pycryptosat 5.17 (CryptoMiniSat 5, default settings, one
thread). Setting: notes/a27.md (Lemma 83), a33.md to a41.md.

## Why this job

Every search in these notes (jobs m8 to m49) used CaDiCaL on a CNF in which each linear condition
over F_2 is cut into parity clauses of at most 4 variables. The instances are mostly such
conditions: (*) and (Q) are sums of products, anisotropy is a chain of sums, and the hints are
linear. After jobs m42 to m46, 54 classes of (B6) and 70 of (B5) are open; the 13 with d = 3 have
never been decided at any budget, and blind budget increases have stopped paying in (B6) (job m45:
5 of 30 at three times the budget). A solver that reasons about XOR constraints natively
(CryptoMiniSat) has never been tried here. This job measures it before anything depends on it.

## Arms and instances

    cadical   m42.py's solver on m42.py's CNF, 2 calibration classes, at most 300 s: host-speed control
    xor       CryptoMiniSat on the same instance with every linear condition as one XOR constraint
    cms_cnf   CryptoMiniSat on m42.py's CNF: separates the solver from the encoding (3 classes)

    calibration (CaDiCaL UNSAT; wall seconds from jobs m46 and m45a; d = dim(X_1 n R) by hand)
      (B5) o042_c000  43 s d 2   o026_c002  46 s d 1   o013_c002  52 s d 2   o023_c002  67 s d 2
           o036_c000  89 s d 2   o047_c003 175 s d 0   o004_c000 356 s d 2
      (B6) o012_c006 265 s d 0   o012_c003 347 s d 0
      cap for xor and cms_cnf: three times CaDiCaL's time, at least 120 s, at most 600 s
    targets (never decided; xor only, 720 s each)
      (B5) o000_c000 d 3, o020_c000 d 3, o027_c001 d 1;  (B6) o002_c000 d 3, o008_c000 d 1

Worst case 131 minutes of solving, plus at most 13 for the controls.

## Graded (each must hold)

1. --part check: m42.py's classifications of (B5) and (B6), recomputed, give each of the 14 names
   its recorded representative, with kernel X_1, image R and rank 3; d of each equals the hand
   count above; on 160 random small systems and mutations (sat_aniso.random_examples), the XOR
   instance accepts exactly the anisotropic systems, as the CNF does; the planted system at t = 6
   (m42.py) is accepted by its XOR instance; the probe's unit clauses are consistent; the XOR
   instance has fewer variables than the CNF (no chain variables) and at least one XOR constraint.
2. --part controls (xor arm): t = 2, dim V = 2 SAT and verified; t = 2, dim V = 3 UNSAT;
   t = 3, dim V = 3 SAT and verified; t = 3, dim V = 4 UNSAT (A(2) = 2, A(3) = 3); the planted system
   at t = 6 with m42.py's hints SAT and verified (a positive control at full encoding).
3. Any SAT at t = 7 in any arm is verified (a system, anisotropic, in the normal form, rank A_u = 3,
   every rank <= 4). A verified SAT on a calibration class would contradict a CaDiCaL UNSAT: graded
   as a failure, and every CaDiCaL answer of these notes would need re-checking.

A failure of 1 or 2 means a bug: fix it, re-run as -v2, count nothing from this job.

## Exploratory, with the decision rule

Guesses (low confidence; no earlier measurement exists): no SAT. CryptoMiniSat with native XOR
decides 5 to 9 of the 9 calibration classes; the median ratio (CaDiCaL's time / xor time, 0 for an
undecided class) lies between 0.3 and 3. It decides 0 of the 5 targets. The host control lands
within a factor of 2 of the recorded times.

Rule:
- **xor wins** (at least 7 of 9 calibration classes UNSAT and median ratio at least 3, host
  comparable): the open classes go to CryptoMiniSat with native XOR. First the rest of m48 (b and
  c, as new versions with the xor arm), then the (B6) classes with d >= 1 that m49 leaves open,
  then every open class with d = 3.
- **A target closes**: it counts as UNSAT under the same caveats as every solver answer here (no
  proof certificate). If it has d = 3 it is the first d = 3 class ever decided; then all 13 d = 3
  classes go to the xor arm at the same budget.
- **Otherwise**: the solver lever is recorded as measured and dropped; CaDiCaL stays.
- cms_cnf is reported only (it says whether a gain comes from the solver or from the encoding).
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
