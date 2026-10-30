# m127 predictions (written 2026-10-30 ~16:40 UTC, before the jobs ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Job m127 (8 shards a-h, 2 cases
each, one case at a time; CaDiCaL 3,600 s and drat-trim 5,400 s per case; the second case starts
only before 9,000 s) takes the 16 d = 1 cases of (B7)_8 that m120m, m120n and m120p left without a
checked certificate: 15 SKIPPED for time and 1 UNKNOWN at 1,800 s (r3b_t8_B7_o009_c006_t2_m031,
three cases sharing its job). Checked certificates stand at 3,830 of 3,876 (notes/a120.md).

1. Tests, check and controls pass in all 8 shards (the bookkeeping checks included: 16 open cases,
   2 per shard, none VERIFIED before, none among m110's 3,408). p = 0.85.
2. At least 14 of the 16 cases VERIFIED. p = 0.75. All 16. p = 0.5.
3. Shard a's former UNKNOWN case (t2_m031) is VERIFIED, with CaDiCaL under 1,800 s alone. p = 0.6.
4. No NOT_VERIFIED and no SAT anywhere. p = 0.95.
5. No shard stopped for memory (4 GB, one drat-trim at a time). p = 0.85.
6. Median CaDiCaL time over the VERIFIED cases below 1,000 s (m120o: 765 s with three at a time).
   p = 0.6.

Decision rules: every VERIFIED case is counted in (note a121). A case still SKIPPED or UNKNOWN
after m127 goes to a one-case job with CaDiCaL at 6,000 s and drat-trim at 9,000 s (as m126d). Once
all 3,846 UNSAT answers have certificates, reconcile the tally against the full d = 1 case list in
one job before any claim about the class.
