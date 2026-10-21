# Job m52: predictions, written 2026-10-20 before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0.

Job m52 (cube_groups/m52.py) checks by machine the class count of Proposition 30
(notes/a42.md), done by hand with Burnside's lemma: the possible maps A_n (n in ker phi outside
span(u)) of the three classes of (B6) with d = 3 at t = 7, dim V = 9, up to the stabiliser G of
(x0, P, A_u) and n -> n + u. The job finds G by solving its linear conditions, not from the
parametrisation used by hand.

## Graded (each must hold)

1. Structure, for each kind: rank A_u = 3, ker A_u = X_1 = span(e_0, e_1, e_2, e_6), R inside X_1,
   and the kind (R inside P; x0 in R; neither) as named.
2. |G| = 86016 (kind P), 12288 (graph), 12288 (L), and every element found fixes x0, keeps P
   and commutes with A_u.
3. The set of maps counted (A x0 = 0, image in R, rank on X_1 at most 2, not 0, not A_u) has
   344 * 512 - 2 = 176126 elements in each kind, and G keeps it.
4. Every orbit has constant rank on X_1, its size divides 2 |G|, and the sizes add up to 176126.
5. Kind P: **40 orbits**, 6 / 20 / 14 with rank on X_1 equal to 0 / 1 / 2.
6. Kind graph: **178 orbits**, 18 / 94 / 66 with rank on X_1 equal to 0 / 1 / 2.

## Not graded

- Kind L was not counted by hand. Guess (low confidence): between 120 and 260 orbits, since its
  stabiliser has the same order as the graph kind's.
- Run time: under 10 minutes in all.

## Rule

If 1 to 6 hold, the next job (m53) runs m42.py's instance for each of the 40 classes of kind P
((B6) pair orbit 1) with A_(h_1) fixed to the orbit representative, after a check that m42.py's
normal form uses no symmetry beyond x0, P and A_u (otherwise the representatives would have to be
taken under the smaller group that is left). Its budget and predictions are written before it is
queued. If 5 or 6 fails, the hand count is wrong somewhere; the note is corrected from the
machine count before anything depends on it.
