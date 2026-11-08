# m134 pre-registration: mop-up and shorter census jobs for the d = 0 cases of (B7)_8

MV2 of Munim, Inc. (mv2@munimtech.com), written 2026-11-08 before any m134 job ran. Made with AI
agents working in MV2's name; no human mathematician has checked this. Code cube_groups/m134.py
(Apache-2.0), text CC BY 4.0. Continues m133 (m133-predictions.md, notes a129 to a138).

## What m134 does

The same certification as m133 (m113.certify at the sweep CNF: CaDiCaL with an ASCII DRAT proof,
then drat-trim; the proof is checked and deleted), in jobs of about 8 to 10 cases instead of 29:

- **mopup**: every case of m133 shards 0 to 21 that has no VERIFIED row in the published cert
  files cube_groups/results/m133/m133s00_cert.json to m133s21_cert.json. The list is rebuilt from
  those files at run time, hard cases first (UNKNOWN, DRAT_STOPPED, ERROR), then the cases that
  never ran, and split into 10 strided chunks (chunk c takes list[c::10]). Caps: CaDiCaL 4,000 s,
  drat-trim 6,000 s, and 10,000 s for a DRAT_STOPPED case.
- **part**: one third of an m133 shard K >= 25 (m133.shard_cases(K)[P::3]), with m133's caps
  (CaDiCaL 1,500 s, drat-trim 4,000 s).

Each job starts no new case after 12,000 s and saves its rows after every case. The cert step
runs only if every gate of the check step passed.

## Gates (check step; the cert step refuses to run if one fails)

1. all 22 cert files of shards 0 to 21 are published;
2. they hold exactly 564 VERIFIED rows for the cases of those shards (a138: 670 certified, minus
   the 6 pilot cases and the 100 of m132);
3. the mop-up list has exactly 76 cases (640 cases in shards 0 to 21, minus 564);
4. exactly 6 of them are hard: 5 UNKNOWN and 1 DRAT_STOPPED (a132, a137, a138);
5. the job's cases are distinct d = 0 cases, none in the pilot or m132, names match (as m133);
6. CaDiCaL and drat-trim are built.

## Predictions (graded over all 10 mop-up chunks together, once all have run)

1. The gates pass in every chunk.
2. m113's controls pass in every chunk.
3. No row ends in ERROR.
4. At least 95% of the 70 cases that never ran before are UNSAT and VERIFIED (over shards 0 to 21,
   564 of the 570 cases that finished were VERIFIED, about 99%).
5. The DRAT_STOPPED case (r3b_t8_B7_o012_c003_t2_m116) is VERIFIED with the 10,000 s drat-trim
   limit.
6. At least 2 of the 5 UNKNOWN cases end UNSAT and VERIFIED at the 4,000 s CaDiCaL limit. (A
   guess: these cases stopped at 1,500 s, and nothing is known about how much longer they need.)
7. Every case starts within 12,000 s in at least 8 of the 10 chunks.
8. No case is SAT, so no solution appears.

For **part** jobs, m133's six predictions apply to each third, with prediction 5 read as "every
case of the third starts within 12,000 s".

## Decision rule

- Gate 1, 2 or 3 fails: no case runs; find out why (a missing or changed file), fix the list, and
  re-file under a new version. Nothing is counted.
- A case ends SAT: stop the census, check the model against the CNF and the class by hand
  (m132.is_solution), and report it as a candidate counterexample, not as a result.
- A case is still not VERIFIED after its mop-up chunk: it goes to a later job with a longer limit
  or another solver. It is never counted as refuted.
- Shards 25 to 47 run as thirds (m134 part) from now on, so that no census job runs longer than
  about 4 hours.
