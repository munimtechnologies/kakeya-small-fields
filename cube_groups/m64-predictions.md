# Job m64: predictions, written 2026-10-21 ~01:20Z before it ran and before m61 or m62 reported

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m64 (cube_groups/m64.py) runs the rank-0 sweep of notes/a52.md: for each open class of A_u,
one instance, m42's instance of the class plus unit clauses that make A_n vanish on X_1 for every
n in N = ker phi (42 clauses in (B6), 63 in (B5)). It needs no symmetry argument: it is the case
"every element of N has rank 0 on X_1". If it is UNSAT, Lemma 93 (a) lets h_1 have rank at least 1
on X_1, so the class's second-matrix split needs only its representatives of rank 1 and 2.
Staged, not queued, on 2026-10-21 (4 jobs pending); the next run queues it, at most 2 new jobs.

- m64a: the 51 open classes of (B6) with d <= 2 (13 with d = 2, 31 with d = 1, 7 with d = 0),
  CaDiCaL, at most 150 s each (51 x 150 s = 127.5 minutes of the 150).
- m64b: the 7 open classes of (B5) not yet split by a finished job (o000_c001, o000_c002,
  o002_c001, o020_c000 with d = 3; o004_c001, o005_c005, o006_c000 with d = 2), CaDiCaL for at most
  600 s, then, if open, the XOR arm for at most 600 s.
- If m61 or m62 has closed some of these classes by the time m64 is queued, they stay in: the
  sweep is then a control with a known answer (UNSAT).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m57.py's own check, unchanged (14 checks, the planted control at t = 6 in both arms).
2. m58's (B6) lists: 23 + 28 classes, disjoint, none closed before; every A_u has kernel X_1,
   the image R of its pair, rank 3, and d as in the hand table of the pairs, d <= 2.
3. Every (B5) class has the kernel and image of its pair and rank 3.
4. On the first class of each group, in both arms: the sweep instance is m42's instance followed
   by exactly 42 ((B6)) or 63 ((B5)) negative unit clauses, one on each entry of A_(v_1), ...,
   A_(v_(kd-1)) in the columns of X_1 other than x0, consistent; same variables and hints (79 or 111).
5. Any SAT at t = 7 is verified as in m57. A verified SAT would be an anisotropic system with
   t = 7 and dim V = 9, a candidate for A(7) = 9: re-check by an independent brute force first.

## Exploratory, with the decision rules

Guesses (low confidence; nothing like this has been run):

- **m64a: at least 25 of the 51 sweep instances UNSAT at 150 s.** The whole classes stayed open
  at 624 s of CaDiCaL and 176 s of XOR; the sweep fixes 42 of the 98 entries of A_(v_1), A_(v_2),
  and with (L) and m42's hints it forces beta(v_1, v_2) = 0.
- **m64b: at least 4 of the 7 UNSAT after both arms.**

Rules:

- **Sweep UNSAT for a class:** its second-matrix split runs only the representatives of rank 1
  and 2 on X_1 (for (B6) d <= 2 after the machine count of Proposition 33; for (B5) from m55's
  lists). A class whose split is already running (o000_c001, o000_c002 in m62): its rank-0
  instances count as closed by the sweep.
- **Sweep open:** the rank-0 instances of that class's split carry Lemma 93's clauses (m63's
  pattern) if m63 shows they help, as m63's rules say.
- **Most of m64a open (more than 40 of 51):** the sweep is not a lever for (B6) at this budget;
  write that down and go to the machine count of Proposition 33 and the splits ordered by size.

No speed-up is claimed before the run. Every UNSAT is a solver answer saved without a proof
certificate. An UNKNOWN is not evidence either way.
