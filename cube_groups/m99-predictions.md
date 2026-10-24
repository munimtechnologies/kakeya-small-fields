# Job m99: predictions, written 2026-10-24 in the run that started at 06:44Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m98a and m98b came back (notes/a91.md): every graded check held (316 and 164). So type (N4) at
(t, dim V) = (8, 11) is empty (Proposition 37) and no element has rank 4 there (Corollary 122), both
computer-assisted. By Proposition 36, A(8) <= 10 now holds if the rank-3 configurations (B7)_8
(p = 7) and (B6)_8 (p = 6) are empty. Lemma 101 (by hand, a91.md) counts their pairs
(ker A_u, Im A_u): 13 and 51.

Job m99 (cube_groups/m99.py) runs m42's classification, unchanged and downloaded from the
repository, at (t, p) = (7, 6), (7, 5), (8, 7) and (8, 6). It sorts every pair orbit by side
(alpha: ker A_u inside span(x0) + P; beta: not) and kind (P, L, graph for Im A_u inside
span(x0) + P; out for Im A_u not inside it), as in the proofs of Lemmas 83 and 101. Then it runs a
pilot: the first class of the first three pairs of each shape at (8, 11), with m42's encoding and
hints, 240 s each.

## Graded (each must hold)

- Unit tests pass (7).
- For each of the four (t, p): the classes are valid (sizes add up to 168 per pair, every member has
  the right kernel and image, every random unit lies in its group, class sizes divide the order of
  the stabiliser, pair orbit sizes divide |G|, every representative has rank 3); the orbit sizes
  add up to (number of X_1) x (number of R); the split by side and kind equals hand_breakdown; the
  orbit sizes of X_1 equal hand_by_x. (4 checks each, 16)
- t = 7: 13 pairs and 68 classes for (B6), 49 pairs and 420 classes for (B5), as job m42a found.
  (2)
- t = 8 (Lemma 101): |G| = 163849992929280 for p = 7 and 2580314849280 for p = 6; 13 and 51 pairs;
  X_1 orbits {11811: 13} and {651: 20, 11160: 31}. (6)
- Every pilot SAT answer is a verified anisotropic system in the normal form. (one per SAT answer;
  none expected)

## Exploratory

- **All 24 graded classification checks hold: about 85%.** The split by kind at t = 7 has never
  been compared with the hand count before (only the totals were); it holds there: about 90%.
- **The t = 8 classification finishes within 30 minutes: about 80%.** Each X_1 orbit at t = 8
  closes 97155 subspaces R under 64 random units.
- **(B7)_8 has between 55 and 80 classes of A_u: about 60%.** (At p = t - 1: 66 classes for 11
  pairs at t = 6, 68 for 13 at t = 7.)
- **(B6)_8 has between 330 and 480 classes: about 55%.** (At p = t - 2: 401 for 39 pairs at t = 6,
  420 for 49 at t = 7.)
- Every class split is "stable" (64 units give the same classes as the first 32): about 85%.
- **Pilot: all 6 instances UNKNOWN at 240 s: about 65%. At least one UNSAT: about 30%. Any SAT:
  about 1%.** (At t = 7, m42a decided 4 of 34 classes of (B6) at about 200 s each.)
- Peak memory at most 2 GB: about 85%.

## Decision rules

- **Every classification check holds:** Lemma 101 is matched by machine; the classes become the
  base of the (B7)_8 and (B6)_8 searches. If the pilot decided nothing, the next step is hand work
  first, as at t = 7: the analogues of Lemma 88 (Lemma 30 for elements of ker phi), Corollary 60
  (h -> A_h one-to-one on ker phi) and Lemma 93 (the second element h_1 of largest rank on ker A_u),
  then a second-matrix split counted by hand before any large solve. If the pilot closed some
  instances within 240 s, the next job gives every class of (B7)_8 a first pass, as m42a did.
- **A t = 7 control fails** (pairs or classes differ from m42a): the downloaded m42.py or its
  environment differs from the one m42a ran. Nothing at t = 8 counts until that is explained.
- **A t = 8 count differs from Lemma 101:** if the machine has more pairs and some split was not
  stable, the random units missed part of the stabiliser; re-run with more units. Otherwise the
  hand count is wrong somewhere: find the step before using the classes.
- **A pilot SAT answer that verifies:** an anisotropic system with t = 8 and dim V = 11 exists,
  so A(8) = 11; check it by brute force and against every lemma it would contradict before saying
  so.
