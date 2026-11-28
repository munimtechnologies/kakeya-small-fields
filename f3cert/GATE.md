# f3cert, execution amendment (2026-11-28, before any LP result was seen)

By MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked it. Code Apache-2.0, text CC BY 4.0.

The pre-registered experiment (PREREG.md, v1.12.0) was filed as a scipy job on a shared compute
queue that has not started it (memory). This amendment changes **how** it is executed, not what
is tested or how outcomes are read:

- `dlp.py`: a pure-standard-library dual simplex with cutting planes replaces scipy's HiGHS.
  Objectives are entropies (cost >= 0), so the all-slack basis is dual feasible and every iterate
  is dual feasible. Each reported bound is recomputed in exact rational arithmetic from the
  solver's dual vector (`exact_bound`), which is valid for any non-negative dual vector. A solver
  bug or a time-out can therefore only weaken a bound, never make it wrong. `status` records
  whether the LP reached its optimum over the whole row pool (`optimal-all`) or stopped early.
- `gaterun.py`: the same configurations, rows, variants, control, alarms and outcome codes as
  PREREG.md, run under a time budget as plain unit tests (`test_run_five.py`,
  `test_run_aug.py`, `test_run_std.py`). Two fixes to the replay: the zero space (h = 0) is
  ignored in the residual, and a certificate row that cannot be rebuilt is reported rather than
  stopping the run.
- One extra row pool, named `cross`, is added and reported separately. For each certificate row
  (K, i, j) it adds the other five pairs among the four F_3-lines i, j, i+j, i-j of span(i, j),
  in intersection form.
- `checkres.py` / `test_results.py`: before results are committed, every exported certificate's
  bound is recomputed from its listed rows and boxes without the LP code, the control must
  certify 1, and the verdict must follow from the numbers. This is an arithmetic check only. Before
  any record claim, an independent re-derivation of the entropy classes from the configuration
  is still required, as PREREG.md says.

Unchanged: F3_RECORD needs an exact bound above 1/1.8263483657186 = 0.547540 (beta_3 > 1.82492);
F3_GAIN needs a bound above the certificate's own 1/C by more than 10^-6; UNSOUND is any
symmetric bound above 0.579380 (the KLSS construction).
