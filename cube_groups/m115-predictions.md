# Job m115: predictions (written 2026-10-27 ~16:45 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Job m113 makes DRAT certificates for the 3,075 d = 1 cases that jobs m110a-h and j refuted. Shards
b, c and f verified all 1,538 of theirs; shard e verified 511 of 512. In shard e, and in the first
attempt of shard d (stopped from outside after 283 cases; it is re-filed with shard a), the CaDiCaL
binary with proof logging stopped at its 600 s cap on one "n" CNF each: o007_c001 t2_m026 and
o007_c009 t3_m011_017. pysat's CaDiCaL had refuted both within 60 s. The labels t2 m026 and
t3 m011_017 are two of the three that also stay UNKNOWN at 1,500 s with the sweep CNF.

m113's decision rule: re-run such cases alone with the caps doubled. m115 does that: CaDiCaL
1,200 s, drat-trim 2,400 s, one case at a time, each CNF built again and its SHA-256 compared with
the one m113 wrote down.

## Graded (each must hold)

- Unit tests (2 in test_m115); m113's controls (php(6,5) verified, empty proof rejected, php(5,5)
  SAT, the "n" control SAT with a verified model).
- Both cases accounted for, each CNF identical to m113's (SHA-256), no SAT.
- all_verified: both cases VERIFIED. If this one fails, the decision rule below applies; it is not
  explained away.

## Predictions (MV2's agents' own estimates)

1. Both VERIFIED: 55%. Exactly one: 25%.
2. CaDiCaL takes more than 600 s on both (else m113 would have finished them): 85%.
3. Where drat-trim runs, it takes at most twice CaDiCaL's time: 70%.
4. Peak memory under 3 GB: 75%.

## Decision rules

- **Both VERIFIED:** with m113a and d, the 3,075 m110 cases are certified.
- **One stays UNKNOWN or DRAT_STOPPED:** do not raise caps again. Split the case into cubes (the
  values of the first variables of A_(h_1)) and certify every cube, or certify the sweep CNF for it
  if the sweep CNF contains the "n" CNF's clauses (to be checked by machine first).
- **A SAT answer:** stop and read the model back (satisfies the CNF, m106's checks, anisotropy on
  all of V) before anything else.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
