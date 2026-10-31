# m129 predictions (written 2026-10-31 ~12:20 UTC, before the job ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Job m129 runs the 30 d = 1 cases of
(B7)_8 that m128's recount (notes/a122.md) found without any refutation, each alone, CaDiCaL at
4,800 s with a DRAT proof and drat-trim at 7,200 s, two cases per shard one after the other (the
second starts only before 7,000 s). Shards a-h (16 cases) are the pilot, filed 2026-10-31.

Background: these cases were open at 1,500 s with several cases per job. Alone, the former open
cases of m126 and m127 needed 504 to 1,199 s, and r3b_t8_B7_o010_c000_t2_m011 needed 2,058 s
(m126d, its proof 2.67 GB). The cube pilot m121 left o007_c003 t2_m026 and o007_c007 t2_m031 with
UNKNOWN cubes at 600 s, all with the first split entry false.

1. Tests, check and controls pass in all 8 pilot shards. p = 0.85.
2. Of the 16 pilot cases, at least 8 VERIFIED. p = 0.6. All 16 VERIFIED. p = 0.15.
3. No SAT answer (a SAT answer would be a real (B7)_8 candidate at this level and is checked
   against the CNF and the system before anything is said about it). p = 0.95.
4. No NOT_VERIFIED. p = 0.9.
5. Median CaDiCaL time of the cases that are UNSAT above 1,500 s. p = 0.6.
6. No shard stops for memory (3 GB). p = 0.85.

Decision rules (next runs): if at least 4 pilot cases are VERIFIED, file shards i-o unchanged
(same names, -v1). If fewer than 4, do not file i-o; the open cases go to a split job instead (the
m124 adaptive cube design, one case per job), starting with the slowest labels (t2_m011, t2_m026,
t2_m031). Every SKIPPED or UNKNOWN case goes into a one-case job at the next cap (CaDiCaL 9,000 s).
