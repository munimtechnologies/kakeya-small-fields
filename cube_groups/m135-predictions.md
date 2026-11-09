# m135 pre-registration: late mop-up of the d = 0 census of (B7)_8, scope "a"

MV2 of Munim, Inc. (mv2@munimtech.com), written 2026-11-09 before any m135 job ran. Made with AI
agents working in MV2's name; no human mathematician has checked this. Code cube_groups/m135.py
(Apache-2.0), text CC BY 4.0. Continues m133 and m134 (m133-predictions.md, m134-predictions.md,
notes a129 to a141).

## What m135 does

m134's mop-up covers m133 shards 0 to 21 only. m135 does the same for later census jobs. A
**scope** is a fixed set of published cert files with the counts expected in them. The job rebuilds
from those files, at run time, the list of cases that have no VERIFIED row (cases that did not
start before their job's start limit, cases whose job was stopped from outside, and cases that
ended UNKNOWN, DRAT_STOPPED or ERROR), hard cases first, then the rest, sorted, and splits it into
strided chunks. The certification is m134's mop-up, unchanged: m113.certify at the sweep CNF
(CaDiCaL with an ASCII DRAT proof, then drat-trim; the proof is checked and deleted), CaDiCaL
4,000 s, drat-trim 6,000 s (10,000 s for a DRAT_STOPPED case), no new case after 12,000 s, rows
saved after every case.

**Scope "a"**: the cert files of m133 shards 22, 23 and 24 (results/m133/m133s22_cert.json to
m133s24_cert.json) and of m134 part k25p0 (results/m134/m134k25p0_cert.json), 97 cases in all.
Split into 3 chunks (chunk c takes list[c::3]: 8, 7 and 7 cases). Job names m135a00 to m135a02.

## Gates (check step; the cert step refuses to run if one fails)

1. all four cert files are published;
2. they hold exactly 75 VERIFIED rows for their cases (shard 22: 23, shard 23: 29, shard 24: 18,
   k25p0: 5; a139 and a141);
3. the mop-up list has exactly 22 cases (6 + 0 + 11 + 5);
4. none of them is hard (no UNKNOWN, DRAT_STOPPED or ERROR row in these files);
5. the job's cases are distinct d = 0 cases, none in the pilot or m132, names match (as m133);
6. CaDiCaL and drat-trim are built.

## Predictions (graded over the 3 chunks together, once all have run)

1. The gates pass in every chunk.
2. m113's controls pass in every chunk.
3. No row ends in ERROR.
4. At least 21 of the 22 cases end UNSAT and VERIFIED. (Every one of the 75 cases of these files
   that finished was VERIFIED, and so was every one of the 16 cases of m134's mop-up chunks 0
   and 1, a140.)
5. Every case starts within 12,000 s in all 3 chunks (m134's mop-up chunks of 8 cases took 5,100
   to 6,000 s).
6. No case is SAT, so no solution appears.

## Decision rule

- Gate 1, 2 or 3 fails: no case runs; find out why (a missing or changed file), fix the scope, and
  re-file under a new version. Nothing is counted.
- A case ends SAT: stop the census, check the model against the CNF and the class by hand
  (m132.is_solution), and report it as a candidate counterexample, not as a result.
- A case still not VERIFIED after its chunk goes to a later scope with a longer limit or another
  solver. It is never counted as refuted.
- Later stopped or unfinished census jobs get a new scope ("b", ...), pre-registered in the same
  way before it runs.
