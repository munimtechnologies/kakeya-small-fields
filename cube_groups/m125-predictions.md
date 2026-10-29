# Job m125: predictions (written 2026-10-29 ~20:15 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

m120a and m120h-l skipped 42 d = 1 cases for time (11, 15, 1, 3, 8, 4), not for any answer, and
four cases came back UNKNOWN at CaDiCaL's 1,800 s limit (r3b_t8_B7_o007_c004_t2_m031 in m120k,
r3b_t8_B7_o010_c000_t2_m011 in m122a, r3b_t8_B7_o010_c000_t2_m026 in m123a,
r3b_t8_B7_o010_c006_t2_m030 in m123b) (notes/a114.md, a115.md). Each of the 46 already has an
UNSAT answer from a 1,500 s sweep without proof logging; a certificate needs the proof.

Shards a, b, c: 14 SKIPPED cases each, as m120 (CaDiCaL 1,800 s, drat-trim 3,000 s), three at a
time, 230 minutes to start cases. Shard d: the 4 UNKNOWN cases, CaDiCaL 4,800 s, drat-trim
7,200 s, all four at once.

## Graded (each must hold)

- Unit tests (3 in test_m125).
- Check: 42 SKIPPED and 4 UNKNOWN in the grade files, disjoint from each other and from every
  VERIFIED row there; all d = 1 cases; none among the 3,408 that m110a-j decided; shard sizes 14,
  14, 14 and 4; both programs present.
- Controls: php(6,5) UNSAT with a verified proof, an empty proof rejected, php(5,5) SAT, and the
  "n" control o007_c008 t2_m012 SAT with a model that passes m106's checks.
- Every case accounted for; sweep mode; no SAT; the same clause count within each class and kind;
  every case that ran VERIFIED.

## Predictions (MV2's agents' own estimates)

1. Shards a-c: at least 38 of the 42 VERIFIED: 60%. None SKIPPED: 65% (these come from the end of
   the name order, o009-o010, where times are longest: m123b's CaDiCaL median was 1,201 s).
2. Shards a-c: at least one UNKNOWN at 1,800 s: 55%.
3. Shard d: at least 3 of the 4 VERIFIED with the longer limits: 50%; all 4: 30%.
4. No NOT_VERIFIED and no SAT anywhere: 97%.
5. Peak memory under 3 GB in every shard (shard d runs four at once): 75%.

## Decision rules

- **VERIFIED:** count them in (the d = 1 tally of a115.md goes up by each).
- **SKIPPED:** one more follow-up at the same limits.
- **UNKNOWN or DRAT_STOPPED (shards a-c):** into the next long-limit shard, as shard d here.
- **UNKNOWN in shard d (at 4,800 s):** cube that case (split on one variable, m121/m124 style)
  rather than raising the limit again.
- **NOT_VERIFIED or SAT:** stop; a sweep refutation that does not check is an error to trace before
  anything else is counted.

No human mathematician has checked any of it; a certificate certifies the CNF only.
