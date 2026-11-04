# Job m133: predictions (pre-registered 2026-11-04, before any shard ran)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Text CC BY 4.0, code Apache-2.0. Companion note: notes/a129.md.

## What runs

The census of the d = 0 block of (B7)_8 at the **sweep** CNF. The 1,494 d = 0 cases without a
certificate after m131 (m132.remaining()), minus the 100 that m132 certified (m133_done.json,
from results/m132/), leave 1,394, sorted by name. Shard k (k = 0 .. 47) takes census[k::48]
(30 cases in shards 0 and 1, 29 in the others). Each shard runs its cases one at a time with
m113.certify at "sweep": CaDiCaL 1,500 s with an ASCII DRAT proof, drat-trim 4,000 s; no new case
starts after 25,000 s; 1 CPU, 2 GB (m132's peak was 0.69 to 0.75 GB), 540 minutes. Shards are filed a few at a time (00 .. 02 first),
so the shared machine is not monopolised.

## Predictions (per shard unless stated)

1. **check:** the shard's cases are distinct d = 0 cases, none certified before; 100 done, 1,394 in
   the census; tools built. (Expected: holds.)
2. **controls:** m113's controls pass. (Expected: holds.)
3. **no error:** every row is VERIFIED, UNKNOWN, SAT or NOT_STARTED, never ERROR. (Expected: holds.)
4. **every finished case is UNSAT and VERIFIED.** (Expected: holds in each of the first three
   shards with about 85% probability each; m132 had 100 of 100.)
5. **every case of the shard starts** inside 25,000 s. (Expected: holds in about two of three
   shards; m132's per-case wall time was about 640 to 890 s, so 29 to 30 cases need about 19,000 to
   27,000 s.)
6. **no solution** (a SAT row whose model passes every m106 check, anisotropy included).
   (Expected: holds. A solution would mean (B7)_8 is not empty; it would be checked by an
   independent script before any claim.)

## Decision rule

- **4 holds:** keep filing shards (three at a time) until all 48 have run; cases NOT_STARTED go to
  a final mop-up shard. Publish counts as they land.
- **UNKNOWN at 1,500 s:** list it; it goes alone to a long job (CaDiCaL 14,400 s) or to cubing.
- **A SAT row that is not a solution:** stop and find which check fails.
- **A solution:** stop the d = 0 work and re-check the model independently (group order, Omega_1,
  the inequality itself), then write it up.
