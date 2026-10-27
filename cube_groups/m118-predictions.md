# Job m118: predictions (written 2026-10-27 ~22:00 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m113 left out the d = 1 cases of shard m110i, because m110i had been stopped from outside and
was re-filed. The re-filed m110i refuted 333 of its 387 cases: 332 with m106's "n" CNF (about
546,000 clauses, at most 50 s each in pysat) and one with m102's sweep CNF at 120 s. m118 certifies
these 333 exactly as m113 did (same code, same caps: CaDiCaL 600 s, drat-trim 1,200 s for "n" and
1,500 s for the sweep), two at a time, for at most 200 minutes.

## Graded (each must hold)

- Unit tests (2 in test_m118); the check: m110i's grade file gives 333 cases, 332 "n" and 1 sweep,
  all d = 1 cases, none among m113's 3,075; both programs present.
- m113's controls: php(6,5) verified, empty proof rejected, php(5,5) SAT, the "n" control
  o007_c008 t2_m012 SAT with a verified model.
- All 333 accounted for, no SAT, the same clause count within each class, kind and mode.
- all_verified: every case that ran is VERIFIED. If this fails, the decision rules apply.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds: 55% (m113: 4 of its 6 shards verified everything).
2. At least 330 of the 333 VERIFIED: 85%.
3. No case SKIPPED for time: 85% (m113's shard a: 513 cases in 103 minutes with two workers).
4. Median CaDiCaL time on the "n" cases under 15 s: 80%.
5. Peak memory under 2 GB: 75%.

## Decision rules

- **All verified:** with m113, 3,406 of the 3,876 d = 1 cases have checked certificates (3,408 if
  m115 verifies its two). What is left is the sweep UNSATs (426, sized by the pilot m117) and the
  cases still open.
- **UNKNOWN at 600 s:** re-run alone with doubled caps (as m115).
- **A SAT answer:** stop and read the model back before anything else.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
