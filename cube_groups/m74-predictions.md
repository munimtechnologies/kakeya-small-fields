# Job m74: predictions, written 2026-10-21 ~12:05Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m74 (cube_groups/m74.py) is the machine count of Proposition 34 (notes/a58.md): the
second-matrix split of the three classes of (B5) with d = 2 that are still open at t = 7 and
dim V = 9, r3b_t7_B5_o004_c001, o005_c005 and o006_c000. It imports m55.py unchanged (the job that
matched Proposition 32 by machine for the ten classes with d = 3, 40 of 40 checks) and only sets
its class list and hand orders, and grades d = 2 where m55 graded d = 3. It counts; it solves
nothing.

## Graded (each must hold; a failure means a bug in the code or an error in Proposition 34:
## find which before any split job runs, count nothing)

1. For each class: A_u has rank 3, kernel X_1 = span(e_0, ..., e_3) (inside H0) and image R of its
   pair, and dim(X_1 n R) = 2.
2. |G| = 2048 (o004_c001), 512 (o005_c005) and 1024 (o006_c000), every element checked (g x0 = x0,
   g P = P, g A_u = A_u g, invertible), with a generating set whose closure is all of G.
3. |Adm| = 405566 for each class (Proposition 34 (b)); the action is closed on Adm; m55's fast rank
   test agrees with the slow one on 3000 random maps and its conjugation tables with direct
   conjugation on 300 per generator.
4. Orbit sizes divide 2 |G| and add up to |Adm|; every orbit has one rank on X_1.
5. The lower bound ceil(405566 / (2 |G|)) is 100, 397 and 199 (Proposition 34 (d)), and each class
   count is at least its bound.

## Exploratory (reported, not graded)

Guesses, written from m55's run (orbits / lower bound was 38 to 75 for the six classes with X_1
inside H0, falling as |G| falls; 7 to 31 for the four with X_1 outside it; rank 0 on X_1 was 13 to
20 % of the orbits when X_1 lies in H0):

- **Each class count is between 10 and 80 times its lower bound** (medium confidence): o004_c001
  between 1000 and 8000, o005_c005 between 3970 and 31760, o006_c000 between 1990 and 15920.
- **The three counts add up to between 6000 and 15000** (low confidence).
- **Rank 0 is between 8 and 25 % of each class's orbits** (medium confidence). The rank-0 classes
  are not needed: each class's rank-0 sweep was UNSAT (job m64b), so by Lemma 93 (a) its split
  needs only the classes of rank 1 and 2.
- **Each class takes under 60 s** (m55: 2.8 to 6.9 s per class).

## Rules

- **All graded checks hold:** Proposition 34 (b) and (c) are matched by machine; the next job
  splits the three classes, their rank 1 and 2 classes only, through m67's (B5) split path (m60's
  instances with A_(v_1) fixed to each root, CaDiCaL at 10 to 20 s, the most rank first), about
  2500 to 4600 instances per group by m73's pace rule, smallest class first.
- **A check fails:** no split job until the cause is found; if the hand count is wrong, the note
  says so and Proposition 34 is corrected.

No speed-up is claimed. A count decides no class.
