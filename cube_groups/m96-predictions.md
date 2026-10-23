# Job m96: predictions, written 2026-10-23 in the run that started at 23:15Z, before its job files

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m95 came back (notes/a88.md): every instance was UNSAT (23 of type (N4), all with DRAT proofs
VERIFIED, and 159 with d = 3), but its positive control failed. The pilot's CNF without its 2^11 - 1
anisotropy clauses ("relax") was UNSAT in 0.79 s, and the same at (6, 3) in 0.11 s. By m95's rule
nothing is claimed: a refutation that does not use anisotropy is not what the hand lemmas predict,
and it might come from a wrong clause.

A reading by hand (a88.md) finds (S) and (a) encoded as Lemma 38(a) says. Lemma 38(a) follows from
(Q) and the normal form without anisotropy, so a relax refutation need not be a bug. To find out
which hypotheses it uses, job m96 (cube_groups/m96.py) rebuilds m94's and m95's CNFs clause for
clause and gives every hypothesis group a selector. Per instance it runs:

    bare     (*) alone (no group): must have a model (the zero system satisfies (*))
    full     every group with anisotropy
    relax    every group but anisotropy
    ladder   relax without one family at a time: units (with outside), inv, lin, a, lin + a, shape, nf
    core     a minimal UNSAT set of groups of the relax CNF (deletion in the order a, lin, inv,
             units, outside, shape, nf)

**Group a (job m96a):** (t, k) = (4, 2) with M = N, I + N, E, F, and (6, 3) with (N, N^2), (E_00,
E_11) and (E_00, E_12), all of type (N4). Caps 300 s (bare, full, relax), 30 s (ladder, deletion),
12 minutes per instance. **Group b (job m96b):** (8, 4) with m94's pilot, d = 4 and d = 3 with
f = 1. Caps 600 s and 60 s, 60 minutes per instance.

## Graded (each must hold; a failure means a bug: fix, re-run as -v2, count nothing)

- Unit tests pass (step 1).
- selfcheck: for every instance the label counts per family are as computed by hand, with 2^d - 1
  anisotropy clauses. Every d = 4 CNF is m94.encode_n4's clause for clause, with the same number of
  variables. The sizes match the records: t6_shift 23124 / 136183, t8_n4 142832 / 905882, and
  t8_d3_f1 142880 / 906151 (m95b's d3_o05_f01).
- bare is SAT, with a model whose clauses check (and (*) by brute force for t <= 6), in every
  instance.
- full is UNSAT for every instance with t <= 6 (A(4) = 4 and A(6) = 6).
- relax is UNSAT for t6_shift and t8_n4, as in m95 (another solver, glucose4).
- Every model found (bare, ladder, core deletions) passes its clause check, and the brute-force
  check where it runs.
- Every core found re-solves UNSAT.

Counted in the grade line ("graded N"): in m96a, 15 from the selfcheck (7 label counts, 7
comparisons with m94, 1 size) and 1 + 7 + 7 + 1 + 7 from the run (all instances present; bare,
full, the t6_shift relax, models), plus one per core found: 38 to 45. In m96b, 5 from the selfcheck
and 1 + 2 + 1 + 2 from the run, plus one per core: 11 to 13. The unit tests are a separate step.

## Exploratory

- **relax UNSAT for all four (4, 2) instances: about 70%.** For all three (6, 3): about 75%.
  t8_d3_f1 relax UNSAT: about 70%.
- **Every minimal core contains an inv group: about 75%.** Every minimal core contains a units
  group (units or outside): about 70%.
- **Some minimal core contains no lin and no a group: about 50%.**
- **ladder -inv SAT in every instance: about 70%.** ladder -lin-a SAT in every instance: about 45%.
- **Every core of group a has at most 12 groups: about 60%.**
- **Every core deletion pass completes within its time: about 80% (a), 60% (b).**
- **Peak memory at most 1.5 GB: about 80% (each job).**

## Decision rules

- **A small core whose hypotheses all hold in Case B (that is, each is proved by the hand lemmas
  from anisotropy):** the relax refutation is explained. Next run writes a hand proof of the core's
  contradiction, starting at t = 4, and checks that it generalises to (8, 4). If the hand proof
  holds, the m95 answers count (computer-assisted, Corollary 122 and Proposition 37), with the
  failed control and its explanation stated.
- **A core with a hypothesis the hand lemmas do not give, or a clause that says something else:**
  a bug. Fix the encoder, re-run m95 as -v2, and count nothing from m95.
- **relax SAT at t = 4 or 6 with a checked model:** that model is the positive control m95 lacked
  at that size. Compare with t = 8 before claiming anything.
- **No core, or an incomplete one:** re-run the deletion alone with longer caps (m97).
