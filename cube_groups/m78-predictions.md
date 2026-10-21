# Job m78 (and m75b): predictions, written 2026-10-21 ~20:10Z before they ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m78 (cube_groups/m78.py) is m75.py with its lists rebound. It runs in three groups:

- **m78a and m78b:** the second-matrix split of r3b_t7_B5_o005_c005, the last class of (B5) at
  t = 7 and dim V = 9 not yet split (d = 2, |G| = 512; 7615 classes: 895 of rank 0, 4624 of rank
  1 and 2096 of rank 2 on X_1, matched by job m74). Its rank-0 sweep was UNSAT (job m64b), so by
  Lemma 93 (a) only the 6720 instances of rank 1 and 2 are needed. In m75's order m78a runs the
  first 3360 (all 2096 of rank 2, then 1264 of rank 1) and m78b the last 3360 (all of rank 1).
  The class is empty only if both halves are all UNSAT.
- **m78r:** r3s_t7_B5_o004_c001_a1240 (rank 1, m55 index 262274), the one instance of m75a's 2084
  that was UNKNOWN at its 10 s budget, gets 5 minutes of CaDiCaL and then, only if still open, 5
  minutes of XOR. If it is UNSAT, o004_c001 is empty (m75a's other 2083 were UNSAT).
- **m75b** (cube_groups/m75.py group b, unchanged, queued in the same run): the split of
  r3b_t7_B5_o006_c000 (3654 instances). Its graded checks and rules are in m75-predictions.md;
  its guesses are written here, since that file's guesses were for m75a only.

With these four jobs queued, four are pending (none were before): within the habit of at most four.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m75's check, unchanged, for the group's class: m57.py's 14 checks with the planted control in
   both arms; m55's structure with d = 2; |G| = Proposition 34 (c) (512 for o005_c005, 2048 for
   o004_c001); |Adm| = 405566; class counts by rank on X_1 equal to m74's run; every root
   admissible, of its rank, distinct with its sum with A_u; the plan (one entry per instance:
   3360, 3360 or 1, the most rank first); hints 111 and units 49 on the first instance in both arms.
2. m78's own: for m78a and m78b, the 6720 roots of rank 1 and 2 and the half's ranks (2096 + 1264,
   then 0 + 3360); for m78r, m55's root at order 1240 of o004_c001 has index 262274, rank 1 and
   A_(h_1) = 134381568, as m75a recorded.
3. Any SAT at t = 7 is verified as in m57. A verified SAT would be a candidate for A(7) = 9 (or an
   error in Lemma 93 or Proposition 34): re-check by an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses:

- **m78r: a1240 UNSAT within the 5 minutes of CaDiCaL: about 85%.** Every leftover re-run at 300 s
  so far closed (67 of 67); its first try ended exactly at its 10 s budget, not far past it, so
  this does not look like a container pause.
- **o005_c005: at most 3 open in each half: about 70%. Both halves all UNSAT (the class empty after
  one pass): about 35%.** m75a, the first (B5) class with d = 2 split, left 1 of 2084 open.
- **o006_c000 (m75b): empty after one pass about 40%; at most 10 open about 70%.**
- **Median UNSAT wall at most 3 s in every group (high confidence).** m75a: 0.97 s.
- **No SKIPPED instance in m78a, m78b or m75b: about 90%.** At m75a's pace (2305 s for 2084
  instances, 1.11 s each) a half of 3360 needs about 62 minutes of the 150, and m75b about 68.
- **Open instances, if any, are of rank 1 on X_1 (low confidence):** m75a's one open was.

Rules:

- **Every instance of a class UNSAT (both halves for o005_c005; m75a plus m78r for o004_c001):**
  the class is empty, (B5) goes up by one, the next corollary.
- **1 to 30 open:** re-run each with 5 minutes of CaDiCaL, then 5 of XOR, as m78r does. **More
  than 30:** read them by rank first, and look at a third-matrix split by hand before queueing more.
- **If a1240 stays open after 10 minutes:** it is the first leftover that did not close at 300 s.
  Write it down, do not count o004_c001 as empty, and look at a third-matrix split of that one
  instance by hand.
- **If all three (B5) classes close:** (B5) is closed (420 of 420), and only (B6) stands between
  the notes and A(7) <= 8. Re-read every dependency before writing that down.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate. An
UNKNOWN is not evidence either way.
