# Job m114: predictions, written 2026-10-27 in the run that started at 03:05Z, before the jobs ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Shard m110i and shards m112a-h came back (notes/a105.md). m110i refuted 333 of its 387 d = 1 cases
and left 54 open. m112a-h ran m102's sweep CNF at 1,500 s: 231 UNSAT, 10 UNKNOWN, 26 skipped when
the shard's time ran out, no SAT. Their UNSAT times had medians of 779 to 915 s per shard and a
maximum of 1,492 s. All ten UNKNOWN cases carry one of three labels: t2 m011 (4), t2 m026 (4) and
t3 m011_017 (2). m112i-l are still in the queue.

Job m114 (cube_groups/m114.py, shards a to f) imports m100.py to m106.py and m110.py to m112.py
unchanged and reads the published grade files of m110i and m112a-h. It runs the sweep CNF at
1,500 s on the 80 cases that have not had it: the 54 m110i left open and the 26 m112a-h skipped.
Of the 80, 16 carry one of the three labels above (11 from m110i, 5 from m112).

## Graded (each must hold)

- Unit tests pass (5 in test_m114) in each job.
- Check: the nine grade files load; 54 open in m110i and 26 skipped in m112a-h, disjoint, 80 in
  all, none with an UNSAT answer in those files, all among the 3,876 d = 1 cases with k <= 4; this
  shard's size (14 in a-b, 13 in c-f).
- Controls: m110's three controls (o000_c000 t2_m511, o011_c000 t3_m001_016, o007_c008 t2_m012)
  SAT at "n", each model verified outside the encoder.
- No ERROR; every SAT model verified; every case of the shard ran or was skipped for time.

## Exploratory

- UNSAT for at least 85% of the cases that ran (all six shards): about 60%. At least 70%: about
  85%. Every case: about 10%.
- At least half of the UNKNOWN answers carry the labels t2 m011, t2 m026 or t3 m011_017: about
  70%.
- Median UNSAT wall time between 700 and 1,000 s: about 60%.
- No shard skips a case: about 75%.
- A SAT answer: about 2%. A model anisotropic on all of V: about 1%.
- Peak memory at most 1.2 GB in every shard: about 90%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11. Re-check it by
  brute force in a separate job before saying anything.
- **Every case UNSAT:** with m112i-l, every d = 1 case except the UNKNOWN ones at 1,500 s is
  decided; DRAT certificates for them follow (sweep CNF, as m113 does for the m110 cases).
- **UNKNOWN cases at 1,500 s (here, in m112a-h and in m112i-l):** no longer cap. Split them (cube
  and conquer: fix the action of T(N)'s generators on Q / pi(R), or the first values of A_(h_1))
  and solve the cubes, or look for a hand lemma on the three labels if they stay the only ones.
- **Fewer than 70% UNSAT:** the open m110i cases are harder than m112's; study the labels before
  any more compute.
