# Job m122: predictions (written 2026-10-28 ~14:30 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

m120b, m120c and m120d (notes/a110.md) VERIFIED 43 sweep certificates and skipped 38 cases when
their 190 minutes ran out. Their check part also showed that m120's case list missed 15 refutations:
those of m111b (7) and m111c (8), which no job has certified. m122 certifies these 53 in three
shards (a, b 18 cases, c 17), two at a time, as m120 does it: m102's sweep CNF (which implies every
CNF of m111), CaDiCaL at 1,800 s, drat-trim at 3,000 s, no case starting after 230 minutes.

## Graded (each must hold, in every shard)

- Unit tests (3 in test_m122). m113's controls: php(6,5) verified, empty proof rejected, php(5,5)
  SAT, the "n" control o007_c008 t2_m012 SAT with a verified model.
- Check: 15 cases decided by m111b-c; 38 SKIPPED in m120b-d; the two sets disjoint; none of the 15
  VERIFIED by m120b-d; 53 in all, all d = 1 cases, none among the 3,408 that m110a-j decided; this
  shard's share as listed.
- Every case of the shard accounted for, in sweep mode, no SAT, the same clause count within each
  class and kind.
- all_verified: every case that ran is VERIFIED. If this fails, the decision rules apply.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds in all three shards: 55%.
2. At least 50 of the 53 VERIFIED: 45%. At least 40: 75%.
3. No case SKIPPED in any shard: 40% (m120b-d averaged about 13 minutes per case with two workers,
   so 18 cases need about 240 minutes against a 230-minute start window).
4. The 15 m111 cases, refuted at in4/out3 or the sweep at 600 s, are VERIFIED with a median CaDiCaL
   time under m120b-d's sweep median (about 700 s): 50%.
5. Peak memory under 2 GB in every shard: 85%.

## Decision rules

- **All VERIFIED:** with m120e-h, m120a's re-run and m120i-p, every one of the 3,846 d = 1
  refutations will have a checked certificate; Proposition 40 then waits only on the 30 UNKNOWN
  cases (m121's cube-and-conquer pilot).
- **SKIPPED:** the skipped cases join the next follow-up job, with those m120e-h skip; no cap is
  raised.
- **UNKNOWN or DRAT_STOPPED:** re-run that case alone at 2,400 s and 4,800 s; if it stops again, a
  cube split with one DRAT proof per cube.
- **A SAT answer:** stop and read the model back before anything else. A SAT sweep CNF on a case
  that m111 or the sweep refuted would mean an error in an encoder.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
