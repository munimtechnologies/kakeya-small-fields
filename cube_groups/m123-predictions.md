# Job m123: predictions (written 2026-10-28 ~17:30 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

m120e, m120f and m120g VERIFIED 48 sweep-CNF DRAT certificates (17, 13, 18) and skipped 30 cases
(9, 13, 8) for time, not for any answer (notes/a111.md). m123 certifies those 30 as m120 does it
(CaDiCaL at 1,800 s, drat-trim at 3,000 s), in two shards of 15, three cases at a time, with 230
minutes to start cases.

## Graded (each must hold)

- Unit tests (3 in test_m123).
- Check: 30 skipped and 48 VERIFIED in the grade files of m120e-g, disjoint; all d = 1 cases; none
  among the 3,408 that m110a-j decided; shard sizes 15 and 15; both programs present.
- Controls: php(6,5) UNSAT with a verified proof, an empty proof rejected, php(5,5) SAT, and the
  "n" control o007_c008 t2_m012 SAT with a model that passes m106's checks.
- Every case accounted for; sweep mode; no SAT; the same clause count within each class and kind;
  every case that ran VERIFIED.

## Predictions (MV2's agents' own estimates)

1. Every graded check holds in both shards: 65%.
2. All 30 VERIFIED (none SKIPPED): 55%.
3. At least one DRAT_STOPPED or UNKNOWN: 20% (these cases come from the end of the name order,
   o009 and o010, where m120f's times were longest).
4. Peak memory under 3 GB with three cases at a time: 80%.

## Decision rules

- **All VERIFIED:** count them in; with m122 and m120a, h and i-p the d = 1 refutations are then
  all certified or queued.
- **SKIPPED:** one more follow-up, at four cases at a time if memory allows.
- **DRAT_STOPPED or UNKNOWN:** re-run that case alone with drat-trim's cap doubled; nothing is
  counted as certified until drat-trim says VERIFIED.
- **NOT_VERIFIED or SAT:** stop; a sweep refutation that does not check is an error to trace before
  anything else is counted.

No human mathematician has checked any of it; a certificate certifies the CNF only.
