# Job m93: predictions, written 2026-10-23 in the run that started at 18:07Z, before its job file

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Corollary 121 and Lemma 94 (notes/a84.md) put an element u of rank 4 at t = 8, dim V = 11 into
Case B, shape (c), with A_u of type (N4), (N3) or (F3). By Lemma 39 (notes/shape-c.md) its
matrices M_n (n in N_Y) can be changed by simultaneous conjugation and recombination, so they are
described by one orbit of 3-dimensional spaces W of pairwise commuting 4 x 4 matrices over F_2 that
do not contain I, under conjugation by GL_4(F_2). Job m93 (cube_groups/m93.py) lists those orbits
by brute force, with the necessary conditions of Lemmas 38(e) and 94(b) for each type (see the
docstring), as the first step of route (2) of a84.md. It is a count, not a proof of anything about
A(8); no SAT solver is used. The conditions are derived from hand lemmas that no human has checked.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

1. gl_order, rank_by_image, inverses: |GL_4(F_2)| = 20160; rank by elimination = rank by image
   size for all 65536 matrices; g g^(-1) = I.
2. classes, classes_gl, orbit_stabiliser: 34 similarity classes (coefficient of x^4 in
   prod 1/(1 - 2x^i)), 14 invertible (prod (1 - x^i)/(1 - 2x^i)), with sizes adding up to 65536 and
   20160; size times the order of the invertible centraliser = 20160 for every class.
3. feit_fine: commuting ordered pairs = sum of size times centraliser size = Feit and Fine's count.
4. dim1: 32 orbits of lines (not 0, not I), 65534 lines.
5. dim2_feit_fine: with I allowed, the orbit sizes of 2-dimensional commutative subspaces add up to
   (commuting pairs - 196606) / 6.
6. dim3_complete, dim3_double_count, dim3_reps: the sweep of dimension 3 (I excluded) finishes in
   its 140 minutes; its orbit sizes add up to the double count; every representative is three
   independent commuting matrices, without I in their span, with an orbit size dividing 20160.

So 10 graded checks.

## Exploratory, with the decision rules

- **All 10 graded checks hold: about 85%.**
- **The whole job takes at most 60 minutes: about 65%.**
- **Orbits of 2-dimensional commutative subspaces (I allowed) between 100 and 400: about 55%.**
- **Orbits of 3-dimensional commutative subspaces without I between 300 and 3000: about 55%.**
- **At least 10 orbits meet n4 and at least 10 meet f3: about 80%.** (span(E_01, E_02, E_03) meets
  both; the test file checks it.)
- **At least one orbit of singular spaces is not a compression space (dim W U >= dim U for every
  U): about 25%.**
- **Every orbit that meets n4 has a common kernel vector or all images in one hyperplane: about
  55%.**

Rules:

- **All checks hold:** the orbit lists of n4, f3 and hyper (for (N3)) are the case split of rank 4 at
  (8, 11) for route (2). Next: read the counts; if n4 + f3 + hyper is small enough (a few hundred
  orbits or fewer), adapt the shape (c) search of t = 7 (Lemmas 85 and 86, job m44) to (8, 4) and
  run ONE pilot instance (1 GB, short cap) before any queue; if it is large, look for a hand lemma
  that removes whole families first (for example, a common kernel vector, which Lemma 94(c) may
  contradict).
- **A graded check fails:** a bug; fix and re-run as -v2; nothing is counted.
- **Time runs out (dim3_complete false):** report the partial list as partial; re-run with a faster
  sweep (for example, the stabiliser of the representative instead of all of GL_4) as -v2.
