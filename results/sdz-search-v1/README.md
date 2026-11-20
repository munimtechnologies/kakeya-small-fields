# sdz-search-v1: graded NO_GAIN (two-dimensional laws do not beat the record for Erdos #1097)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Licence: CC BY 4.0 (text), Apache-2.0 (code `sdz.py`).

Pre-registration: `notes/prereg-sdz.md` (filed 2026-11-19 before the run). Ran 2026-11-19
23:30 to 2026-11-20 00:27 UTC (1 CPU, 1 GB; peak memory 0.01 GB); `test_sdz.py` passed first.
Output: `sdz.json`. Every alpha below is the 50-digit evaluation of explicit printed weights, so
each one is a valid lower bound for the Katz-Tao sum-difference constant C_3b.

## Calibration

E0, Lemm's printed weights: alpha = 1.7789757584. E1, optimal weights on staircases:

| points | alpha |
|---|---|
| 5 | 1.7787361302 |
| 7 | 1.7789883385 |
| 9 | 1.7789886983 |
| 11, 13, 15 | 1.7789886983058502 (converged) |

The 7-point optimum is above the calibration bar 1.778980, so the run is valid.

## Second-order test of the tensor product p x p (E2)

kappa = alpha * Lambda_max(sum_j lambda_j A_j x A_j) on mean-zero x mean-zero directions.
kappa > 1 would mean a two-dimensional correlation improves the product law.

| staircase | KKT weights (X, Y, X+Y) | kappa | best direct 2-D optimum | gain over 1-D | verdict |
|---|---|---|---|---|---|
| 7 points | 0.3766, 0.3766, 0.2468 | 0.9064074 | 1.7789883385 | 0 | STABLE |
| 9 points | 0.3766, 0.3766, 0.2468 | 0.9064078 | 1.7789888274 | 1.29e-7 | UNCLEAR |
| 11 points | same | 0.9064078 | 1.7789887834 | 8.5e-8 | UNCLEAR |
| 13 points | same | 0.9064078 | 1.7789887831 | 8.5e-8 | UNCLEAR |

kappa is about 0.906 on every staircase, so p x p is a strict local maximum under
two-dimensional correlation, with a 9% margin. The three UNCLEAR verdicts come from the
pre-registered rule (a direct 2-D gain above 1e-9 together with kappa < 1): optimisation from a
random start left the neighbourhood of p x p and found laws on S x S that beat every 1-D
staircase by up to 1.29e-7. These are non-local moves, not second-order ones. They still stay
below the record.

## Annealing (E3, E4)

E3, 40 minutes over supports in Z^2 (difference box [-2, 6]^2): best 1.7789535499 (52 points).
E4, 15 minutes in one dimension: best 1.7789813590 (7 points).

## Grade (rule fixed in advance): NO_GAIN

Best verified value: 1.7789888273727827 (E2, 9-point staircase squared, random start). That is
below the literature record 1.7789888414 (Mosaic Intelligence 2026, 13 points) and far below
the RECORD bar 1.7790. The weak prediction (STABLE everywhere) held for the second-order part
(kappa < 1 on all four staircases) and failed as a formal verdict on three of four, because of
the non-local gains.

What it means: pairing two copies of the record law does not help to second order, so the
stalled lower bound (1.77898 since Lemm 2015) will not move by adding a correlated second
coordinate. Laws on Z^2 that are far from products come within 1.4e-8 of the record, so the
remaining slack below the record is tiny and seems to need a new kind of law, not more
dimensions. The upper bound is 1.8263484 (Farnamfar, arXiv:2611.19594).
