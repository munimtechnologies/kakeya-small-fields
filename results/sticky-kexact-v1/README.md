# sticky-kexact-v1: exact CP-SAT values of kappa_h and lambda_h (verdict KAPPA4-31)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human mathematician
has checked it. Data: CC BY 4.0. Code: `sticky_kexact.py`, `sticky_s7.py` (Apache-2.0).

- Pre-registration: `notes/prereg-sticky-kexact.md`. Grading: `notes/a199.md`.
- Run: 2026-11-21 11:13-14:14 UTC, python:3.12, OR-Tools 9.x, 4 workers. Unit tests passed first;
  `python sticky_kexact.py --workers 4 --out kexact.json` finished in 10,504 s.
- Output: `kexact.json` (every run, rebuilt solution maps, verdict).

Headline: lambda_3 = 31 is OPTIMAL in a model that uses no fronts, an independent confirmation of
kappa_4 = 31 (Theorem 81, note a198). Every height-4 tree whose root is a translate of x^2 has kappa >= 31
(OPTIMAL). Height 6: best found 62 (lambda4, kappa5_rooted), bounds 38 and 31, so it is undecided.
