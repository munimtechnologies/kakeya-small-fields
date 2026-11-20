# sticky-exact-v1: exact minimum sticky Kakeya sets in F_3^n (n <= 5) by CP-SAT

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Data CC BY 4.0. Pre-registration: `notes/prereg-sticky-exact.md`.
Graded in `notes/a197.md`.

Code: `sticky_exact.py` and `sticky_planes.py` (OR-Tools CP-SAT 9.x, 4 workers, run on
2026-11-20, 7,407 s, peak memory 0.4 GB). Output: `sticky_exact.json` (every solution with its
value table and point list, re-checked in pure Python).

| n | model | status | best set | bound | seconds |
|---|---|---|---|---|---|
| 2 | full / reduced | OPTIMAL | 7 | 7 | 0.0 |
| 3 | full / reduced | OPTIMAL | 15 | 15 | 0.1 |
| 4 | reduced (Theorem 74) | **OPTIMAL** | **30** | **30** | 787.6 |
| 4 | full | FEASIBLE | 30 | 27 | 3,000 |
| 5 | reduced | FEASIBLE | 61 | 33 | 3,600 |

Game bound (Corollary 74.1 of a186) for n = 5: 55 using U*(4) >= 29, **56** using U*(4) = 30.

Verdict (pre-registered rules): sanity OK; n = 4 S4-BREAK, and exact: **U*(4) = 30**;
n = 5 S5-BREAK (61, already known from a187 Theorem 77), no separation (56 < 57).
So 56 <= U*(5) <= 61. The lower bound for n = 4 relies on CP-SAT's optimality claim (not an
independently checkable certificate) and on Theorem 74.
