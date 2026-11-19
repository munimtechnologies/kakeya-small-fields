# Pre-registration: sdz-search-v1 (is the sum-difference constant attained in one dimension?)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Licence: CC BY 4.0 (text), Apache-2.0 (code `sdz.py`).
Written 2026-11-19, before the job ran.

## The question

The Katz–Tao sum-difference constant C_3b is the least C with
H(X−Y) ≤ C · max(H(X), H(Y), H(X+Y)) for integer random variables with X−Y determining (X, Y).
It is also the exponent in Erdős problem #1097 (how many common differences of 3-term
progressions n integers can have; Koishi Chan's observation on the erdosproblems.com forum).

| side  | value | source |
|---|---|---|
| lower | 1.725982 | Ruzsa (3 points) |
| lower | 1.77898 | Lemm, Proc. AMS 2015 (7 points, "staircase" x + y ∈ {1, 2}) |
| lower | +1e-8 | AlphaEvolve (Georgiev, Gómez-Serrano, Tao, Wagner, arXiv:2511.02864) |
| lower | 1.7789888414 | Mosaic Intelligence 2026 (13 points; replayed by C. Toledo) |
| upper | 11/6 | Katz–Tao 1999 |
| upper | 1.8272962 | Tomar 2026 |
| upper | 1.8263484 | Farnamfar, arXiv:2611.19594 (Nov 2026) |

Every known lower-bound law is **one-dimensional** and near Lemm's staircase. AlphaEvolve's
laws "resembled discrete Gaussians" and gained only in the eighth decimal. The lower side
has stalled at 1.778988. We ask whether a law on Z^2 that is not a tensor product can do
better. (Any finite configuration in Z^2 embeds in Z by a Freiman isomorphism, so such a law
is a legitimate lower bound for the integer problem.)

## Second-order criterion (exact; the job evaluates it)

Let p be an optimal law on a staircase S, with KKT weights λ = (λ_X, λ_Y, λ_S) (summing to 1)
and ratio α. For laws on S × S near p ⊗ p, the entropy H and each form entropy lose the mutual
information between the two coordinates. To second order, for a correlation perturbation C
(mean zero in each coordinate) the Lagrangian changes by
(ε²/2)(α Σ_j λ_j ‖(A_j ⊗ A_j)C‖² − ‖C‖²), where A_j = E[· | form j] in L²(p).
So p ⊗ p is **not** a local maximum, and a better two-dimensional law exists, iff
κ := α · Λ_max(Σ_j λ_j A_j ⊗ A_j) > 1 on mean-zero ⊗ mean-zero.

Hand estimates at Lemm's printed weights (before the run):
- KKT weights from the gradient equations: λ_S ≈ 0.247, λ_X + λ_Y ≈ 0.753. The three
  coordinate equations are consistent to 4 digits.
- The parity direction C = π ⊗ π (π = parity of D, which is S-measurable): η_X(π)² ≈ 0.0756,
  so κ ≈ 1.779 · (0.753 · 0.0756 + 0.247) ≈ 0.54.
- The smooth direction g = D − E D: η_X(g) ≈ 0.736 (same for Y) and η_S(g) = 0, so κ ≈ 0.73.
- The maximal correlation of X and Y under Lemm's law satisfies ρ² ≤ 0.266 (trace bound), so
  the X/Y block alone gives at most α(λ_X+λ_Y)(1+ρ²)/2 ≈ 0.85. A crude bound on the cross terms
  with the parity block allows κ up to about 1.09, so the hand estimates do not settle it.
- **Prediction (weak):** STABLE (κ < 1) on every staircase.

## What the job runs (`sdz.py`, standard library; tests `test_sdz.py`)

- E0: Lemm's printed weights (expected alpha ≈ 1.77898).
- E1: optimal weights on staircases of 5, 7, …, 15 points.
- E2: for the staircases of 7, 9, 11 and 13 points, κ by power iteration (two seeds), and
  direct optimisation of all weights on S × S from four starts: the product, the top
  eigen-direction, and two random perturbations.
- E3: 40 minutes of simulated annealing over supports in Z^2: a difference box [−2, 6]², each
  difference d either absent or given a sum s ∈ [0, 3]² of the same parity
  (x = (d+s)/2, y = (s−d)/2). Start: the product of two Lemm staircases.
- E4: 15 minutes of the same in one dimension: d ∈ [−4, 10], s ∈ [−1, 4].
- Every reported number is the 50-digit evaluation of explicit printed weights, so each is a
  valid lower bound for C_3b whatever the optimiser did.

## Decision rules (fixed now)

- INVALID: the 7-point staircase optimum is below 1.778980 (calibration). Then fix the code and
  re-file as v2; no conclusions.
- **RECORD:** some law has verified alpha_s > 1.7790. Next: an exact rational certificate
  (separate job using interval arithmetic), note a189, and the research article. This would be
  the first real improvement of the lower bound since 2015.
- FRONTIER: best in (1.7789888414, 1.7790]. Report only; an eighth-decimal gain is not a result.
- NO_GAIN: otherwise.
- Tensor verdict per staircase: UNSTABLE if κ > 1 + 1e-6 and a direct 2-D gain > 1e-9; STABLE
  if κ < 1 − 1e-6 and no gain > 1e-9; else UNCLEAR. If every staircase is STABLE, we report
  that the record laws are second-order stable under two-dimensional correlation: evidence
  (not proof) that pairing two copies cannot help, and a pointer to where a new idea must come
  from.

Output: `/out/sdz.json` (field `grade`, `tensor_verdicts`, `E1_staircases`, `E2_tensor`,
`E3_anneal_2d`, `E4_anneal_1d`).
