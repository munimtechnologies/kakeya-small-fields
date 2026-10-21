# Job m55: predictions, written 2026-10-20 ~17:50Z before it ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: m55.py (Apache-2.0, stdlib
only). Setting and proofs: notes/a45.md, Proposition 32.

## Graded (each must hold)

For each of the ten classes of (B5) with d = 3 (pair orbits 0, 1, 2, 20, 31, 32, 33):

1. structure: rank A_u = 3, ker A_u = X_1, Im A_u = R, R inside X_1, and X_1 inside
   H0 = span(e_0, ..., e_5) exactly for pair orbits 0, 1, 2.
2. group: every solution kept satisfies g e_0 = e_0, g P inside P, g A_u = A_u g, and |G| is
   24576 (o000_c000), 8192 (o000_c001), 8192 (o000_c002), 24576 (o001_c000), 24576 (o002_c000),
   4096 (o002_c001), 3072 (o020_c000), 512 (o031_c000), 1536 (o032_c000), 512 (o033_c000).
3. maps: |Adm| = 405566 for pair orbits 0, 1, 2 and 323966 for 20, 31, 32, 33; the fast count
   agrees with a direct rank computation on 3000 random maps; the conjugation tables agree with
   direct conjugation; G maps Adm into itself.
4. classes: every class has constant rank on X_1 and a size dividing 2 |G|; the sizes add up to
   |Adm|.

A failure of 2 or 3 means an error in Proposition 32 (or in the code): find it before any count
is used.

## Reported, not graded

The number of classes of each, by rank on X_1, with one representative each. Lower bounds
ceil(|Adm| / (2 |G|)): 9, 25, 25, 9, 9, 50, 53, 317, 106, 317. Guess (low confidence): 800 to 2000
for the nine classes not yet UNSAT in all (all but o031_c000).

## Rule

- All graded checks hold: no instance job for (B5) with d = 3 until job m53 or m54a shows that the
  split instances of (B6) close (at least 30 of m53's 40 or at least 60 of m54a's 89 UNSAT). Then
  the classes with at most about 100 instances go first, one job per class, with representatives
  from this job's output; pair orbits 32 and 33 wait for a hand fact or a third fixed matrix. A
  class that m48b or m48c closes is dropped.
- If m53 and m54a show that the split does not close (B6) instances, the route is set aside for
  (B5) too.
