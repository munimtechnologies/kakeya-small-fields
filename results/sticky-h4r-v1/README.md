# sticky-h4r-v1: exact height 3, relaxed above -> pi_5 = 29,791 (with a196)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked it. Data CC BY 4.0; code (`sticky_h4r.py`, `sticky_h3.py`) Apache-2.0.

- Pre-registration: `notes/prereg-sticky-h4r.md`. Grading and theorem: `notes/a198.md` (Theorem 81,
  Proposition 94).
- Run: 2026-11-20, 12:03-12:10 UTC, python:3.12, 1 CPU; `python -m unittest -v test_sticky_h4r`
  (passed), then `python sticky_h4r.py --out h4r.json --tlimit 9000 --h6 1` (272 s).
- `h4r.json` keys: `game` (a190 checks), `height3` (E3 = 112 minimal vectors, kinds, search stats,
  complete), `height4` (F4 = 670 vectors, least product 4,096), `height5` (least quadratic-root product
  29,791 with witness and derivation from real height-3 trees; affine bound 36,864;
  `pi5_lower_bound` 29,791), `verdict` PI5-OPEN, `bugs` [], `height6` (F5 = 3,361 vectors, least
  product 29,791; `pi6_lower_bound` 216,000).

Together with the a196 tree G (slices 31, 31, 31), the lower bound gives **pi_5 = 29,791 exactly**.
