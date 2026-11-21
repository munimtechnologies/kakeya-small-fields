# sticky-l4-v1: can height 6 beat 31^(1/5)? (verdict UNDECIDED)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human mathematician
has checked it. Data: CC BY 4.0. Code: `sticky_l4.py` with `sticky_s7.py`, `sticky_kexact.py`,
`sticky_h3.py`, `sticky_h4r.py` (Apache-2.0).

- Pre-registration: `notes/prereg-sticky-l4.md`. Grading: `notes/a199.md`.
- Run: 2026-11-21 06:32-13:23 UTC, python:3.12, OR-Tools 9.x. Unit tests passed first. The container hit
  its 360-minute limit during the last step (kappa5), so the job is marked failed (exit 124); every
  finished step had already been written to `l4.json`.
- Output: `l4.json` (fronts, every run, rebuilt solution maps, verdict).

Headline: the fronts of sticky-h4r-v1 were reproduced exactly (E3 = 112 complete, F4 = 670, least product
4,096). The capped lambda_4 <= 61 model found no solution and proved only 28 in 11,401 s, so whether a
height-6 tree beats the a196 base stays open (60 <= kappa_5 <= 62).
