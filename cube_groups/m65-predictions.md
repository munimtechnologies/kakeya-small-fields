# Job m65: predictions, written 2026-10-21 ~02:45Z before it ran and before m62 or m64 reported

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m65 (cube_groups/m65.py) carries out a rule that job m61 wrote down before it ran
(m61-predictions.md): "SKIPPED classes and the 5 with d = 0: the next job, unchanged, 15 minutes
each." The setting is in notes/a42.md, a50.md, a53.md and a54.md.

## What m61b found (graded 2026-10-21 ~02:30Z, all 22 checks held, no SAT)

- The 16 classes of (B6) with d = 1 of job m47's list, CaDiCaL 15 minutes each, whole budgets only:
  4 UNSAT (o007_c002 843.8 s, o007_c003 781.3 s, o007_c006 646.5 s, o007_c009 428.7 s),
  7 UNKNOWN at 900 s (o007_c001, o007_c007, o008_c004, o009_c000, o009_c001, o009_c002, o009_c003),
  5 SKIPPED (o009_c005, o010_c004, o010_c006, o010_c007, o010_c008). Guess (1 to 5) held.
- (B6) moves from 17 to 21 of 68.

## The plan

- One group: the 5 classes m61b skipped (d = 1), then the 5 classes with d = 0 of m47's list
  (o011_c002, o011_c003, o012_c004, o012_c009, o012_c011), CaDiCaL 15 minutes each, 152 minutes in
  all, so all 10 fit even if every one runs to its cap.
- The 7 classes m61b left open are not in this job: by m61's rule they join the second-matrix split
  of Proposition 33 (a52.md).

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. m61.py's own check, unchanged (22 checks: m57.py's 14, the kind-L setting, m47's list with d by
   hand, both probes).
2. m61b's 4 UNSAT + 7 open + 5 skipped are exactly the 16 classes with d = 1 of m47's list; this
   job's 5 classes with d = 0 are exactly those of m47's list; none is in the closed list or in m45's.
3. The plan is the 10 classes in this order, each with d = 1 or 0 as its group says.
4. Any SAT at t = 7 is verified as in m57 (a system, anisotropic, normal form with A_u fixed,
   rank A_u = 3, every rank <= 4). A verified SAT would be a candidate for A(7) = 9: re-check it
   with an independent brute force before any claim.

## Exploratory, with the decision rules

Guesses (low confidence):

- **d = 1: 1 to 3 of the 5 UNSAT.** m61b's rate at 15 minutes was 4 of 11 that ran.
- **d = 0: 2 to 5 of the 5 UNSAT.** m45a closed 4 classes of pair orbit 12 with d = 0 at 624 s;
  these 5 have had only about 250 s of CaDiCaL (m42b) and 176 s of the XOR arm (m58b).
- **The job ends inside its time and no class is SKIPPED.**

Rules:

- **A class UNSAT:** (B6) goes up by one per class.
- **A class still open at 15 minutes:** it joins the second-matrix split of Proposition 33, with
  the rank-0 representatives dropped where job m64a's sweep instance for that class is UNSAT.
- **All 10 open:** 15 minutes of CaDiCaL is no longer a lever for (B6) with d <= 1; no more
  whole-class runs on (B6), only the split, ordered by size, smallest first.
- A SKIPPED class would mean a timing bug (the plan fits by construction): fix, -v2.

No speed-up is claimed. Every UNSAT is a solver answer saved without a proof certificate, as in
every job of these notes. An UNKNOWN is not evidence either way.
