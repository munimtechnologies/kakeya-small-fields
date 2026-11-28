# k34c: every smallest Kakeya set of F_4^3 (pre-registration)

SPDX-License-Identifier: CC-BY-4.0. Made with AI agents working in MV2's name (MV2, Munim, Inc.,
mv2@munimtech.com). Not yet checked by a human mathematician. Written 2026-11-28, before any
result of this search existed.

## Question

The smallest Kakeya set of F_4^3 has 28 points (k34/ and k34b/, two independently written
searches over the hand reduction in k34/PROOF.md). The 28-point Kopparty-Saraf-Sudan (KSS) set
reaches it. **Is the KSS set the only smallest Kakeya set of F_4^3, up to affine maps and the
field automorphism (the group of order 64 * 181,440 * 2)? If not, what are the others?**

In the plane the analogous question is settled: Blokhuis and Mazzocca (arXiv:0911.4370) showed
that for even q the Kakeya sets of the minimum size q(q+1)/2 are exactly those that come from a
dual hyperoval, and Blokhuis, De Boeck, Mazzocca and Storme (Des. Codes Cryptogr. 72, 2014)
classified the next sizes. We found no classification of smallest Kakeya sets in any
three-dimensional space over a field with more than two elements (searches of 2026-11-28).

## Method

Phase 1 (classify.py, resumable over several gate sessions): the k34b search with threshold
T = 29 (every branch whose lower bound is at most 28 is explored). At each complete map f with
optimal value 28, every placement of the five horizontal lines reaching 28 is listed and its
point set recorded.

Why that lists every 28-point Kakeya set up to the symmetries already used:
1. A 28-point Kakeya set K is the union of one line per direction (that union is a Kakeya set
   inside K, and no Kakeya set has 27 points).
2. A smallest plane of K has at most 6 points. If every plane had at least 7, every plane would
   have exactly 7 (each parallel class of 4 planes splits the 28 points). Count the pairs of
   distinct points of K inside a common plane: there are 5 planes through two points, so the sum
   over the 84 planes of x(x - 1) is 28 * 27 * 5 = 3,780. With x = 7 everywhere it would be
   84 * 42 = 3,528. Contradiction.
3. Move a smallest plane (r <= 6 points) to z = 0. The 16 non-horizontal lines meet it in the
   image S0' of f, with r' <= r <= 6 points. The plane group (5,760 maps) moves S0' to its orbit
   representative and a shear makes f(0) = S0'[0]. The k34b bound stays valid with r' because
   every plane has at least r >= r' points, and K, of size 28 < 29, is never pruned.
4. At the leaf for f, K contains the forced points plus one line per horizontal direction, and
   any such union has at least the leaf's optimal value 28 points. So K is exactly one of the
   listed optimal placements.

Phase 2 (later run): sort the listed sets into classes under the full 3-D group with an exact
canonical form, computed as the minimum image over the affine frames of K picked out by
group-invariant point and pair statistics (an equivariant frame set), times the two field
automorphisms. Each class is reported with its invariants: plane-size distribution over the 84
planes, the number of full planes, lines contained, stabiliser order, and whether it is the KSS
class or the even-q construction of Maschietti (J. Combin. Theory Ser. A 2010).

## What counts as the result (fixed now)

- Phase 1 is complete when the progress file says complete. Every listed set must have 28
  points and pass k34b's Kakeya checker, and no leaf may be below 28 (that would contradict
  K(3, 4) = 28).
- Positive control: the KSS class must appear in phase 2. If it does not, the listing is
  wrong and no classification is claimed.
- Result: the number of classes N. N = 1 means the KSS set is the unique smallest Kakeya set of
  F_4^3. N > 1 means there are smallest sets not of KSS type, each published with its points.
- Controls run first: the same listing over F_3 (threshold 14, r' <= 4) must find 13-point sets,
  none smaller, all accepted by the checker; the plane counts 84 / 21 / 5 behind step 2 are
  recomputed.

## Limits

A computer-assisted classification resting on the hand reduction above and in k34/PROOF.md,
and on one program (k34b's search code with a new listing step). Phase 2 must be checked by a
second, independent isomorphism test before any claim.
