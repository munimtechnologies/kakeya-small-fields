# sticky-pair-v1: annealing over pairs of sticky trees (heuristic), graded NOT-FOUND

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked it. Data CC BY 4.0; code (`sticky_pair.py`, `sticky_s7.py`) Apache-2.0.

- Pre-registration: `notes/prereg-sticky-pair.md`. Grading: `notes/a198.md`, section 4.
- Run: 2026-11-20, 12:18-14:00 UTC, python:3.12, 1 CPU; unit tests passed; `sticky_s7.py` (S7
  witness re-check) and `sticky_pair.py --minutes 100`.
- `s7.json`: verdict **S7-TRUE** (the a196 height-5 tree with slices 31, 31, 31 re-verified).
- `pair.json`: height 3 best lambda 31 (the a196 seed; 1,037 restarts, none below 32 on their own);
  height 4 best lambda 62 (the seed (H, H(-d)); 576 restarts ended at 69..114). Rebuilt witnesses:
  N slices (11,20,20) -> triangle (31,31,31); N slices (22,40,40) -> triangle (62,62,62).
  Verdict **NOT-FOUND** (no lambda_3 <= 30, no lambda_4 <= 61).
