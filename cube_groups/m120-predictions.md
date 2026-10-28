# Job m120: predictions (written 2026-10-28 ~02:40 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

After m117, m118 and m119 (notes/a109.md), 3,846 of the 3,876 d = 1 cases with k(T(N)) <= 4 have
UNSAT answers and 3,411 of them have DRAT certificates checked by drat-trim. The other 435 were
refuted only by m102's sweep CNF (about 907,000 clauses) at 1,500 s, by pysat's CaDiCaL. m120
certifies them in 16 shards (a-c 28 cases, d-p 27), two at a time, as m113 certifies, with CaDiCaL
at 1,800 s and drat-trim at 3,000 s, no case starting after 190 minutes. Shards a-h are filed
first; i-p follow once the first shards have run, so the shared machines are not tied up.

## Graded (each must hold, in every shard)

- Unit tests (3 in test_m120). m113's controls: php(6,5) verified, empty proof rejected, php(5,5)
  SAT, the "n" control o007_c008 t2_m012 SAT with a verified model.
- Check: 438 sweep UNSATs in the grade files; m117's three VERIFIED cases among them; 435 left, all
  d = 1 cases, none among the 3,408 that m110a-j decided; this shard's share as listed.
- Every case of the shard accounted for, in sweep mode, no SAT, the same clause count within each
  class and kind.
- all_verified: every case that ran is VERIFIED. If this fails, the decision rules apply.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds in all 16 shards: 45%.
2. At least 430 of the 435 VERIFIED once all 16 shards have run: 60%.
3. No case SKIPPED in any shard: 55%.
4. At least one DRAT_STOPPED or UNKNOWN: 30%.
5. The largest proof is over 2 GB: 25%.
6. Median CaDiCaL time over all shards under 600 s: 65% (m117: 0.49 to 0.66 times pysat's time;
   pysat's median on these cases was about 730 s).
7. Peak memory under 2 GB in every shard: 85%.

## Decision rules

- **All VERIFIED:** 3,846 of the 3,876 d = 1 cases are certified. Proposition 40 then waits only on
  the 30 cases still UNKNOWN at 1,500 s, which go to one cube-and-conquer job.
- **SKIPPED:** the skipped cases go into one follow-up job; no cap is raised for them.
- **UNKNOWN or DRAT_STOPPED:** re-run that case alone with m117's caps (2,400 s and 4,800 s); if it
  stops again, a cube split with one DRAT proof per cube.
- **A SAT answer:** stop and read the model back (it satisfies the CNF, m106's checks, anisotropy on
  all of V) before anything else.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
