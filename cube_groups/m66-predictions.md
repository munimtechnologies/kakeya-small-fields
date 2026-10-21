# Job m66: predictions, written 2026-10-21 ~03:05Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m66 (cube_groups/m66.py) is the machine count of Proposition 33 (notes/a52.md) that a52.md
lists as the step after jobs m63 and m64: for each of the 51 classes of (B6) with d <= 2 that were
open on 2026-10-21 (the 4 closed by job m61b stay in as checks of the count), the group G of
g with g x0 = x0, g P = P, g A_u = A_u g, found by solving these linear conditions (not from the
parametrisation of Proposition 33 (b)), and the classes of Adm under G and A -> A + A_u, by
union-find, as jobs m52 and m55 did for Propositions 30 to 32. It runs no solver. Its output (the
orbit roots, by rank on X_1) is the list of split instances for the classes that stay open.

## Graded (each must hold; a failure is a bug in the code or an error in the hand count: find
## which, correct the note in the open, count nothing until a -v2 holds)

1. The list: m58.py's two lists are 51 classes, the same names as the table of Proposition 33 (c).
2. For each class: rank A_u = 3, ker A_u = X_1 = span(e_0, ..., e_3), Im A_u = the R of its pair,
   and dim(X_1 n R) equal to the hand value of its pair (51 checks).
3. For each class: every element of G fixes x0, keeps P, commutes with A_u and is invertible; and
   |G| equals the order in Proposition 33 (c) (51 checks: 13 with d = 2, 31 with d = 1, 7 with d = 0).
4. For each class: |Adm| = 176126 when d >= 1 and 176128 when d = 0 (Proposition 33 (a)); Adm is
   closed under G; the table form of conjugation agrees with direct conjugation on 200 maps (51).
5. For each class: every orbit has one rank on X_1, its size divides 2 |G|, and the sizes add up to
   |Adm| (51).
6. For the 7 classes with d = 0: the number of orbits is that of Proposition 33 (d): 994, 552, 552,
   3840, 1976, 1288, 553 (9755 in all) (7).

## Exploratory, with the decision rules

Guesses (low confidence):

- **Every hand order in (c) holds.** They were checked by orbit-stabiliser sums on seven pair
  orbits, but pair orbits 7, 11 and 12 could not be completed that way.
- **The 44 classes with d >= 1 have 2 to 8 times their lower bound of 7792 classes** (a52.md's
  guess, unchanged), so the 51 classes have about 25,000 to 70,000 split instances in all.
- **Representatives of rank 0 on X_1 are 5 to 20 percent of the classes with d >= 1** (kind L:
  51 of 308, kind graph: 18 of 178).

Rules:

- **All checks hold:** Proposition 33 (a), (c) and (d) are matched by machine, and the count for
  d >= 1 is new. The split of each open class runs from m66's roots, classes ordered by their
  number of instances, smallest first, with the rank-0 roots dropped where job m64a's sweep instance
  for the class is UNSAT. Classes that close by a whole-class run (job m65) are dropped.
- **An order check fails:** recompute that class's G from the parametrisation by hand and say in
  the next note which was wrong; no split instance of that class runs before a -v2 holds.
- **More than 60,000 instances in all:** at the 1 to 25 s that split instances have taken so far,
  that is several days of one compute slot; run the smallest classes first and write down the
  cost before going on.

No speed-up is claimed. This job decides no class: it only counts.
