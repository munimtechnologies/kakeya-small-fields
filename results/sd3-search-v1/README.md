# sd3-search-v1: graded (no counterexample to Conjecture R3)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Licence: CC BY 4.0.

Pre-registration: `notes/a181.md` (search section). Code: `sd3_search.py`, `sd3_local.py` at the
commit recorded in `results/sd3-search-v1/repo_fetch.json`. Ran 2026-11-19 13:59–16:22 UTC
(1 CPU, 1 GB; peak memory 0.01 GB); the unit tests passed first.

Conjecture R3 says that every configuration in every F_3^N has
H(D) ≤ R0 · avg_t H(Y_t), with R0 = log 27 / log(27/4) = 1.7259824578787…
(Ruzsa's ratio). Equivalently, the sum-difference constant of F_3^N equals Ruzsa's value, and the
entropy Kakeya constant of F_3 equals the KLSS base (27/4)^(1/3) = 1.889882.

| N | maps tried | random | random quadratic | perturbed ρ^N | max F | max R_avg (H(D) > 0.3) | counterexample |
|---|---|---|---|---|---|---|---|
| 2 | 207,090 | 82,601 | 62,185 | 62,304 | 4.4e-16 | 1.7259824578787193 | no |
| 3 | 162,567 | 64,838 | 48,833 | 48,896 | 8.9e-16 | 1.7259824578787195 | no |

Here F = H(D) − R0 · avg_t H(Y_t), so max F is zero to rounding. Many different maps reach exactly R0:
uniform laws on all 9 directions of F_3^2 (the same value as the product ρ^2) and uniform laws
on 3 directions (the value of one Ruzsa triangle). Nothing beat R0.

**Grade (rule fixed in advance): no hit, so this is evidence only.** About 370,000 maps in
dimensions 2 and 3, each with its law optimised by the concave-convex procedure, never exceed
Ruzsa's ratio. Sampling does not cover all maps, so R3 stays open.

Contrast with the integers: there the same problem has constant at least 1.7789888
(Lemm 2015; Mosaic Intelligence 2026). If R3 is true, characteristic 3 has a strictly smaller
sum-difference constant than characteristic 0.

Files: `sd3_n2.json`, `sd3_n3.json` (the best laws found, with weights), `summary.json`.
