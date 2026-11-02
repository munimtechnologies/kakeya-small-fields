# m130 predictions (written 2026-11-02 ~05:45Z, before the job ran)

MV2 of Munim, Inc.; made with AI agents working in MV2's name. Apache-2.0 (code), CC BY 4.0 (text).

Job m130-d0-census-v1: list the d = 0 cases of the rank-0 case of (B7)_8 (the classes of m100's
shards with dmeet = 0, their cases from m102.class_cases with k(T(N)) <= 4 by m105.le4), and run six
of them, spread evenly through the sorted names, at m106's "n" CNF (CaDiCaL 600 s with a DRAT proof,
drat-trim 1,200 s). This is the first job to touch d = 0; every earlier job (m102 to m129) worked on
d = 2 (Proposition 39) or d = 1 (notes/a126.md).

| # | Prediction | Graded by |
|---|---|---|
| 1 | There are d = 0 classes, all with dmeet = 0, with distinct names | `check_d0_classes_nonempty`, `check_d0_all_dmeet0`, `check_names_unique` |
| 2 | They have exactly 1,500 cases with k <= 4 (the figure note a122 gives) | `check_d0_le4_1500` |
| 3 | No d = 0 case name is a d = 1 case name; no t1 case is among them | `check_disjoint_from_d1`, `check_no_t1` |
| 4 | m113's controls pass (the three tool controls; o007_c008 t2_m012 SAT with a checked model) | `controls_*` |
| 5 | At least 4 of the 6 pilot cases are UNSAT at "n" within 600 s | `unsat_at_n_ge_4` |
| 6 | No pilot case is SAT at "n" | `no_sat` |
| 7 | Every UNSAT answer gets a drat-trim VERIFIED certificate within 1,200 s | `all_unsat_verified` |
| 8 | All six rows are present and none is an error | `pilot_all_accounted`, `no_error` |

Why 5 and 6: for d = 1, 3,062 of 3,876 cases (79%) were UNSAT at "n" within 60 s (notes/a104.md),
and the only "n" SAT ever seen is the d = 1 control o007_c008 t2_m012, whose model is not anisotropic
on all of V. I expect d = 0 (the smallest meet) to be at least as constrained, but that is a guess;
the point of the pilot is to measure it.

Decision (pre-registered):
- 2 fails: the 1,500 in a122 was wrong; report the true count, and plan with it.
- 5, 6 and 7 hold: shard all d = 0 cases at "n" (m110's pattern, about 150 cases per shard, 60 s
  then 600 s), then certificates for the UNSAT ones (m113's pattern) and the sweep CNF for the rest.
- A SAT at "n": check its model with m106's checks and report it as such (an "n" model is not a
  counterexample to (B7)_8 until it is anisotropic on all of V); then the sweep CNF for that case.
- Fewer than 4 UNSAT: the d = 0 cases are harder than d = 1; plan the sweep CNF alone, one or two
  cases per job (m129's pattern), before any sharding.
