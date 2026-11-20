# h3scan-v1: graded NO_GAIN (Conjecture C_3(3) holds for every quadratic map of F_3^3)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Licence: CC BY 4.0 (text), Apache-2.0 (code).

Pre-registration: `notes/prereg-h3scan.md` (filed 2026-11-19 before the run). Code: `h3scan.c`,
`h3scan.py`, `run_h3scan.py`, `test_h3scan.py`. Ran 2026-11-19 23:16-23:23 UTC (2 CPUs, 1 GB;
peak memory 0.06 GB). The unit tests passed first. gcc 14.2.0. Output: `h3scan.json`.

For P: F_3^3 -> F_3^3, S(P) = sum over t in F_3 of sum over fibres F of x -> P(x) + t x of
|F| log2 |F|. The Kakeya base bound is 3 * 2^(-S/243), and S = 162 is the KLSS base 1.889882.

| family | maps scanned | complete | above 162 | equal 162 | max S | second-best S |
|---|---|---|---|---|---|---|
| quadratic (Q + L, 15 classes of L) | 5,811,307,335 (covers all 3^27) | yes | 0 | 1,976 (in the scanned representatives) | 162 | 150.793987519 |
| S_3-equivariant, any degree | 387,420,489 | yes | 0 | 54 | 162 | 157.832293922 |
| cyclic, degree <= 3 | 43,046,721 | yes | 0 | 18 | 162 | 143.650825199 |

Every map within 1e-7 of 162 was classified exactly by prime exponents; no map fell in
(162 - 1e-7, 162). Every map in each family's top 8 values was rebuilt and re-scored in
Python with integers: C and Python agree on all of them (`c_and_python_agree: true`).

**Grade (rule fixed in advance): NO_GAIN.** No quadratic map of F_3^3, no S_3-equivariant map
and no cyclic map of degree <= 3 beats KLSS at block length 3. This settles Conjecture C_3(3)
(note a164) for every quadratic map over F_3, the case a164 left open. The prediction (NO_GAIN
for quadratic maps) held.

## Structure read off the output (exact counts)

The 15 classes of linear parts L (under L -> A L A^-1 + lam I) have sizes 3, 351, 351, 312, 1404,
2106, 2106, 2106, 2808, 2808, 1872, 1296, 1296, 432, 432, which add up to 3^9 = 19,683. Maps
reaching S = 162 occur in exactly four classes, the four classes of matrices that are
diagonalisable over F_3:

| L representative | eigenvalues | class size | maps Q + L with S = 162 per L |
|---|---|---|---|
| 0 | (0,0,0) scalar | 3 | 1,872 |
| diag(1,0,0) | (1,0,0) | 351 | 48 |
| diag(2,0,0) | (2,0,0) | 351 | 48 |
| [[0,1,0],[1,0,0],[0,0,0]] | (1,2,0) distinct | 1,404 | 8 |

So exactly 3*1872 + 351*48 + 351*48 + 1404*8 = **50,544** quadratic maps with zero constant term
(1,364,688 with constants) reach 162. Every quadratic map whose linear part is not diagonalisable
over F_3 has S < 162, and every quadratic map has either S = 162 or S <= 150.793987519.
