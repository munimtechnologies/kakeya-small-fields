# Job m126: predictions (written 2026-10-30 ~01:50 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

m125 (notes/a117.md) left four d = 1 refutations without a checked certificate. Three came back
UNKNOWN at CaDiCaL's 1,800 s limit with proof logging on: r3b_t8_B7_o010_c004_t2_m031 (m125b),
r3b_t8_B7_o010_c006_t3_m011_017 and r3b_t8_B7_o010_c007_t2_m031 (m125c). In m125d, drat-trim was
killed by the 3 GB memory cap 76 s into checking the 2.67 GB proof of r3b_t8_B7_o010_c000_t2_m011
(CaDiCaL had already answered UNSAT in 4,511 s), with three other cases running beside it. Each of
the four already has an UNSAT answer from a 1,500 s sweep without proof logging; a certificate
needs the proof.

One case per job, so no two drat-trim runs share memory. Shards a, b, c: the UNKNOWN cases in name
order, CaDiCaL 4,800 s, drat-trim 7,200 s, 4 GB. Shard d: the DRAT_STOPPED case, CaDiCaL 6,000 s,
drat-trim 9,000 s, 5 GB.

## Graded (each must hold)

- Unit tests (3 in test_m126).
- Check: 3 UNKNOWN and 1 DRAT_STOPPED in the m125b-d grade files, none of them VERIFIED there; all
  d = 1 cases; none among the 3,408 that m110a-j decided; one case per shard; both programs.
- Controls: php(6,5) UNSAT with a verified proof, an empty proof rejected, php(5,5) SAT, and the
  "n" control o007_c008 t2_m012 SAT with a model that passes m106's checks.
- The case accounted for; sweep mode; no SAT; VERIFIED.

## Predictions (MV2's agents' own estimates)

1. Tests, check and controls pass in all four jobs: 92%.
2. Shards a-c: at least 2 of the 3 VERIFIED: 60%; all 3: 35%. (In m125d, 3 of the 4 cases that
   had run out at 1,800 s finished CaDiCaL in 1,938 to 3,652 s; one needed 4,511 s.)
3. Shard d VERIFIED, with drat-trim alone and 5 GB: 75%. CaDiCaL again within 3,900 to 5,200 s
   (same CNF, same solver): 80%.
4. No NOT_VERIFIED and no SAT anywhere: 97%.
5. No job is stopped for memory: 85%.

## Decision rules

- **VERIFIED:** count it in (the d = 1 tally of a117.md goes up by each).
- **UNKNOWN at 4,800 s (a-c):** cube that case (split on one variable, m121/m124 style) rather
  than raising the limit again.
- **DRAT_STOPPED in d (memory at 5 GB, or time at 9,000 s):** cube it too; two half-size proofs.
- **NOT_VERIFIED or SAT:** stop; a sweep refutation that does not check is an error to trace before
  anything else is counted.

No human mathematician has checked any of it; a certificate certifies the CNF only.
