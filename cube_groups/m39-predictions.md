# Job m39 (m39a, m39b, m39c): predictions, written 2026-10-19 ~17:30Z before anything ran

MV2 of Munim, Inc. Written with AI agents working in MV2's name. Code: a7_casea.py (Apache-2.0).
Setting: notes/a25.md, Lemma 80 (Case A at rank 4 for t = 7 and dim V = 9, A_u up to the group G
fixing e_0 = x0, D = span(e_1, e_2) and R = span(e_1, ..., e_4)).

## Graded (each must hold; one failure means the encoding or a hand count is wrong)

Selfcheck (pure Python, every job):
1. 20160 candidates A_u (A_u kills e_0, e_1, e_2; image R).
2. Exactly 6 orbits under the 20 generators, each of one class of Pbar (the map induced on R / D),
   the six classes all different: zero, id, f4, unip, idem, nil.
3. Orbit sizes: zero 576, id 1536, f4 3072, unip 4608, idem 6912, nil 3456 (sum 20160); each divides
   |G| = 6^3 x 2^14 = 3538944.
4. Every orbit stays inside the candidates; each representative lies in the orbit of its class.
5. Every generator is invertible, fixes e_0 and maps D into D and R into R.
6. Unit clauses: 112 for the normal form (7 + 49 + 8 x 7), 65 more for the hints.
7. At t = 5 with case_a's parameters, the encoder gives exactly case_a's CNF for all 9 orbits.
8. The planted system (t = 6, three copies of Lemma 63 (ii), u = a_1 + a_2 + a_3) is a system, is
   anisotropic, has phi(h_1) = phi(h_2) = 0, and its assignment satisfies its CNF.

Solver controls:
9. Planted (m39a, m39b): SAT with a verified model (brute-force system check, anisotropic, normal
   form as fixed).
10. t = 5 (m39a only): all 9 orbits UNSAT (Lemma 52; job m15 found the same CNFs UNSAT). UNKNOWN or
    SKIPPED at 3 minutes each (12 minutes in all) is reported and not graded.
11. Any SAT answer at t = 7 must come with a verified model whose ranks are all <= 4
    (Proposition 29(b)). An unverified SAT means a bug: stop and fix before reading anything else.

## Exploratory (the question asked), with the decision rule

Prediction: all 6 classes UNSAT in the plain encoding (m39a: zero, id, f4; m39b: unip, idem, nil),
and all 6 UNSAT in the hinted one (m39c). Confidence: moderate (at t = 6 every Case A instance,
job m24, was UNSAT within seconds; at t = 7 the CNF is larger, dim V = 9).

Rule:
- All 6 plain classes UNSAT, every graded check held: **no element of rank 4 in Case A exists in an
  anisotropic system with t = 7 and dim V = 9** (row 1 of the table in a24.md), computer-assisted,
  resting on Proposition 29(b) and Lemma 77 (a), (c) (which define the candidates), on Lemma 80 and
  on 6 solver answers without proof certificates.
- Plain class UNKNOWN but hinted class UNSAT: the class is closed only on top of the hints, i.e.
  also on (2), (3) and Lemma 77 (a), (d), (f); say so in the note.
- Any class UNKNOWN in both: re-run that class alone with at least twice the budget it had (one or
  two per job), as at t = 6 (jobs m36, m37).
- A verified SAT: an anisotropic system with t = 7 and dim V = 9 exists, so A(7) = 9 (Theorem 29),
  and A(t) = t fails at t = 7. Re-check the model by an independent brute force before any claim.
- Ungraded results (UNKNOWN, SKIPPED, ERROR) are reported, never counted either way.
