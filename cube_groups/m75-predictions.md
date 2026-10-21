# Job m75: predictions, written 2026-10-21 ~18:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m75 (cube_groups/m75.py) splits two of the three classes of (B5) still open at t = 7 and
dim V = 9 by the second matrix A_(v_1) (Proposition 34, notes/a58.md; every hand number matched by
job m74, notes/a64.md). All three have d = dim(X_1 n R) = 2 and a UNSAT rank-0 sweep (job m64b), so
by Lemma 93 (a) only the split instances of rank 1 and 2 on X_1 are needed. Everything but the
lists and the check is m74.py, m55.py, m60.py and m57.py, imported unchanged.

- **m75a:** r3b_t7_B5_o004_c001 (|G| = 2048; 2367 classes: 283 of rank 0, 1448 of rank 1, 636 of
  rank 2): 2084 instances.
- **m75b (written, queued later):** r3b_t7_B5_o006_c000 (|G| = 1024; 4133 classes: 479, 2528,
  1126): 3654 instances.
- o005_c005 (|G| = 512; 7615 classes: 895, 4624, 2096; 6720 instances) is left for two later groups.
- The job files download m55.py, m57.py, m60.py, m74.py and sat_aniso.py from the repository's main
  branch at setup. These are the files jobs m67 and m74 ran.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check (14 checks, with the planted control at t = 6 solved and verified in both
   arms).
2. m55's structure of the class: rank A_u = 3, kernel X_1 = span(e_0, ..., e_3), image R, R not
   inside X_1, dim(X_1 n R) = 2; |G| = Proposition 34 (c) (2048 for o004_c001, 1024 for o006_c000)
   with m55's element-by-element check; |Adm| = 405566 = m55's hand value, with the closed action,
   the fast rank test against the slow one and the conjugation tables; orbit sizes divide 2 |G| and
   add up to |Adm|; class counts by rank on X_1 equal to m74's run.
3. Every root is admissible (m60.admissible), of its recorded rank on X_1 by both rank functions,
   and distinct with its sum with A_u.
4. The plan: exactly the rank-1 and rank-2 roots (2084 or 3654), names distinct, rank 2 first.
5. Hint and unit counts of the first instance: 111 hints, 49 unit clauses for A_(v_1), units
   consistent, in both arms (the XOR arm with native XOR constraints).
6. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 34): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses:

- **o004_c001 empty after this one pass: about 35%. At most 10 open: about 65%.** The split
  instances of the d = 3 classes of (B5) left a few rank-1/2 instances open at 10 to 20 s (m62: 3
  of 1455 in o000_c001 and 5 of 1484 in o000_c002; m67a: 1 of 1615 in o020_c000), and every one
  of those closed at 300 s. These d = 2 classes resisted 10 to 15 minutes of CaDiCaL as whole
  classes (jobs m46, m48), so they may be harder per instance.
- **Median UNSAT wall at most 3 s (high confidence)**; m67a's pace was about 1.45 s per instance
  with overhead (2352 s for 1620 instances).
- **No SKIPPED instance in m75a: about 90%** (2084 instances at m67a's pace is about 50 of the 150
  minutes).
- **Open instances, if any, are mostly of rank 1 on X_1 (low confidence):** 1448 of the 2084 are.

Rules:

- **All split instances of the class UNSAT:** the class is empty, (B5) goes up by one, the next
  corollary.
- **1 to 30 open:** re-run each with 5 minutes of CaDiCaL, then 5 of XOR (on (B5) the XOR arm has
  been a good second pass), in the next job. **More than 30:** read them by rank first, and look at
  a third-matrix split by hand before queueing more.
- **Pace:** median at most 3 s: m75b runs as written, and o005_c005 is split into two groups of
  about 3360. Above 8 s: re-estimate the cost of o005_c005 before queueing it.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
