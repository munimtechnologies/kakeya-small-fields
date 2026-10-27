# Job m116: predictions (written 2026-10-27 ~16:50 UTC, before the jobs ran)

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Shards m112i-k (the sweep CNF at 1,500 s on 99 of the 399 d = 1 cases left open by m110 and m111)
refuted 75, left 10 UNKNOWN and skipped 14 when their 210 minutes ran out. Job m114 (the 54 cases
m110i left open and the 26 m112a-h skipped) refuted 76 of 80, left 4 UNKNOWN and skipped none;
its UNSAT times had a median of about 787 s and a maximum of 1,428 s. Shard m112l was stopped from
outside and is re-filed.

Job m116 (cube_groups/m116.py, shards a and b of 7 cases) runs the same sweep CNF at 1,500 s on the
14 cases m112i-k skipped, two at a time, with a 150-minute budget per shard.

## Graded (each must hold)

- Unit tests pass (3 in test_m116).
- Check: the three grade files load; their skipped cases are exactly the 14 listed in m116.py; none
  has an UNSAT answer there; all are d = 1 cases; 7 in this shard.
- Controls: m110's three controls SAT at "n", each model verified outside the encoder.
- No ERROR; every SAT model verified; every case of the shard ran or was skipped for time.

## Exploratory

- At least 11 of the 14 UNSAT: about 70%. All 14: about 20%.
- No case skipped: about 85%.
- An UNKNOWN case carries one of the labels t2 m011, t2 m026, t2 m031 or t3 m011_017: about 60%
  if any case is UNKNOWN.
- A SAT answer: about 2%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11; re-check it by
  brute force in a separate job before saying anything.
- **UNKNOWN at 1,500 s:** no longer cap; the case joins the cube-and-conquer list with the 24 UNKNOWN
  cases of m112a-k and m114.
