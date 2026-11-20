# kakeya-sparse-v1: Kakeya-restricted entropy LPs on Farnamfar's configurations over F_3

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Data CC BY 4.0. Pre-registration: `notes/prereg-kakeya-sparse.md`.
Graded in `notes/a197.md`.

Run 2026-11-20 (scipy 1.14.1 / HiGHS). Files: `results.jsonl` (one line per tier),
`cert_standard-five-page-t0.json` and `cert_standard-t0.json` (exact certificates rebuilt from the
LP duals and passed by our checker). The job was killed at its 3 GB memory cap during tier tA of
the 18-page configuration.

| configuration | tier | rows | value | exact |
|---|---|---|---|---|
| 5-page | replay of Farnamfar's certificate | 111 | C = 152/83 | yes |
| 5-page | t0 / t0L / tA / tB | 239 - 10,513 | 0.5460526 | 83/152 at t0 |
| 5-page | tC-n (no Kakeya rows) | 15,836 | 0.5460526 | |
| 5-page | tC-u (507 Kakeya rows) | 16,343 | 0.5460526 | |
| 18-page | replay of Farnamfar's certificate | 778 | C = 2762/1509 | yes |
| 18-page | t0 / t0L | 1,579 / 1,804 | 0.5463432 | 1509/2762 |
| 18-page | tA and above | not run (out of memory) | | |

Verdict: H0 passed; NULL for the 5-page configuration at every tier (no gain from F_3 closures,
no effect of the Kakeya restriction); the 18-page configuration reproduces its published value and
is otherwise incomplete. No record.
