# Job m76a-v2: why it was re-queued, written 2026-10-21 ~18:40Z before it ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

m76a-b6split-v1 (the second-matrix splits of o009_c002 and o009_c009 of (B6), 1888 + 1888
instances of rank 1 and 2 on X_1; cube_groups/m76-predictions.md) started on the shared compute
machine at 14:51Z. Its tests and check passed. The solve step was stopped by the host (exit 143)
after 130 of its 150 minutes, so the grade step never ran. Under the playbook's rule a host kill is
not a result, so the job is re-queued unchanged as m76a-b6split-v2. The only difference is that
m57.py, m58.py, m66.py, m69.py, m76.py and test_m76.py are downloaded at setup from the
repository's main branch, where commit 07a52dd and the commits before it put them.

What v1 left on disk (read by hand from its stdout and per-instance files, not graded):

- o009_c002: all 1888 instances ran. 1883 were UNSAT and 5 were UNKNOWN, all of rank 1 on X_1, at
  m66 indices 10288, 14343, 35334, 39940 and 58375.
- o009_c009: 634 instances ran, 633 UNSAT and 1 UNKNOWN (m66 index 16918, rank 2). The other 1254
  were never reached.
- Five of the six UNKNOWNs had wall times far above their 10 s budgets (79 s, 187 s, 197 s,
  1470 s and 2380 s). The parent kills the child at the budget, so time far past it most likely
  means the container was paused or starved; these walls are not evidence about the instances.

Predictions for v2, besides m76-predictions.md, which stand unchanged:

- In o009_c002, at most 5 instances are open, and every open one is among the five above (medium
  confidence: one of them, 14343, ran out its budget in a normal 12.6 s wall, so it may be
  genuinely hard).
- If v2's grade agrees with v1 on o009_c002 (same open set or a subset), that is a second, machine-
  graded run of the same 1883 UNSAT answers, not new evidence about the class.
