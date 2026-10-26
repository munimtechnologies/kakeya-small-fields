# Job m112: predictions, written 2026-10-26 in the run that started at 14:36Z, before the jobs ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m111a-c and m110h, m110j came back (notes/a104.md). m111a confirmed by machine that the cases
m110a-g left open are, with two exceptions, cases where T(N) leaves pi(R) invariant. In the pilot
m111b-c, neither "in4" nor "out3" decided the open cases, but m102's sweep CNF at 600 s refuted 14 of
21, with UNSAT times of 186 to 582 s (median about 490 s). m110h and m110j left 46 and 53 cases
open. m110i is re-filed and not in this job.

Job m112 (cube_groups/m112.py, shards a to l) imports m100.py to m106.py, m110.py and m111.py
unchanged and reads the published grade files of m110a-h, m110j, m111b and m111c. It runs the sweep
CNF at 1,500 s on each of the 399 open cases, two at a time, for 210 minutes per shard.

## Graded (each must hold)

- Unit tests pass (6 in test_m112) in each job.
- Check: the eleven grade files load; 414 cases without an UNSAT answer in m110a-h, j; the 15
  cases m111b-c decided are among them; 399 left, all among the 3,876 d = 1 cases with k <= 4;
  this shard's size (34 in a-c, 33 in d-l).
- Controls: m110's three controls (o000_c000 t2_m511, o011_c000 t3_m001_016, o007_c008 t2_m012)
  SAT at "n", each model verified outside the encoder.
- No ERROR; every SAT model verified; every case of the shard ran or was skipped for time.

## Exploratory

- Exactly two of the 399 do not leave pi(R) invariant (o010_c003 t2_m092 and o010_c008
  t3_m063_205, read off the names): about 95%.
- UNSAT for at least 80% of the cases that ran (all twelve shards): about 50%. At least 60%:
  about 80%. Every case that ran: about 8%.
- Median UNSAT wall time between 300 and 800 s: about 65%.
- Some UNSAT answer above 1,000 s: about 70%.
- t3 cases a higher UNSAT share than t2 cases (pilot: 6 of 7 against 8 of 14): about 65%.
- The labels the pilot left open at 600 s (t2 m012, m015, m026, m031, m047, m059 and t3
  m030_043) a lower UNSAT share than the other labels: about 75%.
- A sweep answer SAT: about 2%. A model anisotropic on all of V: about 1%.
- At least one shard skips a case for time: about 50%.
- Peak memory at most 1.2 GB in every shard: about 85%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11. Re-check it by
  brute force in a separate job before saying anything.
- **Every case decided (with m110i's open cases run the same way):** DRAT certificates for all
  3,876 d = 1 cases, each for the CNF that was UNSAT for it (as m108), then Proposition 40.
- **Most decided, a remainder open at 1,500 s:** no longer cap. Split the remainder (cube and
  conquer: fix the action of T(N)'s generators on Q / pi(R), or the first values of A_(h_1)) and
  solve the cubes, or look for a hand lemma on the labels that stay open.
- **Fewer than 60% decided:** the sweep is the wrong tool for these cases; stop and study the
  labels (the action of T(N) on pi(R) and on Q / pi(R)) before any more compute.
