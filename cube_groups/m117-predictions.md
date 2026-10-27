# Job m117: predictions (written 2026-10-27 ~22:00 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

With job m112l (notes/a107.md), 3,834 of the 3,876 d = 1 cases with k(T(N)) <= 4 have UNSAT
answers, and job m113 has DRAT certificates, checked by drat-trim, for 3,073 of them. 761 are
still uncertified: the 333 that the re-filed m110i refuted, the two that m115 re-runs, and 426 that
only m102's sweep CNF (about 907,000 clauses) refuted at 1,500 s, by pysat's CaDiCaL in 260 to
1,500 s (jobs m112a-l and m114a-f). Proposition 40 needs a checked certificate for every case, as
Propositions 38 and 39 had. Nobody has measured yet what one of these certificates costs. This pilot
measures it on three of m112l's sweep UNSATs before about 760 are filed:

| case | kind | sweep clauses (m112l) | pysat CaDiCaL (m112l) |
|---|---|---|---|
| o007_c005 t2_m034 | t2 | 907,089 | 260 s (m112l's fastest) |
| o009_c002 t3_m004_034 | t3 | 906,105 | 422 s |
| o010_c000 t2_m047 | t2 | 907,113 | 713 s (m112l's median) |

They run one at a time, fastest first, as m113 certifies (CNF built again, CaDiCaL binary with an
ASCII DRAT proof, drat-trim, proof deleted once checked), with CaDiCaL at 2,400 s and drat-trim at
4,800 s. No case starts after 150 minutes.

## Graded (each must hold)

- Unit tests (2 in test_m117). m113's controls: php(6,5) verified, empty proof rejected, php(5,5)
  SAT, the "n" control o007_c008 t2_m012 SAT with a verified model.
- All three cases accounted for, in sweep mode, each CNF with m112l's clause count, no SAT.
- all_verified: all three VERIFIED. If this fails, the decision rules apply. It is not explained
  away.

## Predictions (MV2's agents' own estimates)

1. All three VERIFIED: 50%. At least one: 80%.
2. The CaDiCaL binary with proof logging takes longer than pysat's CaDiCaL did, on each verified
   case: 65% (m113/m115: proof logging and a different version; two "n" CNFs went from < 60 s to
   > 600 s).
3. drat-trim takes at most twice CaDiCaL's time: 55%.
4. The largest proof is over 2 GB: 50%; over 8 GB: 15%.
5. Peak memory under 3.5 GB: 70%.

## Decision rules

- **All three VERIFIED with wall time per case at most 3x pysat's time:** file the full run of
  about 760 cases (sized from per_case: proof size decides workers per shard, at most one sweep
  proof at a time if over 2 GB).
- **Verified but slower than 3x, or a proof over 8 GB:** certify the "n"-mode UNSATs (m110i) first,
  and for the sweep cases try a smaller certificate: a cube split (values of the first variables of
  A_(h_1)) with one DRAT proof per cube.
- **UNKNOWN or DRAT_STOPPED:** do not raise caps again; cube split as above, pilot on this case.
- **A SAT answer:** stop and read the model back (satisfies the CNF, m106's checks, anisotropy on
  all of V) before anything else.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
