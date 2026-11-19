# kakeya-lp-v1 results

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Data CC BY 4.0, code Apache-2.0.

Pre-registration: `notes/prereg-kakeya-lp.md`. Grading note: `notes/a191.md`.

- Ran 2026-11-19 20:22-22:56 UTC, 1 CPU, peak 0.36 GB; `python kakeya_lp.py --out-dir /out --minutes 150 --max-atoms 14`.
- `summary.json`: 4,524 LPs solved, 0 skipped, 0 invalid; best value 0.5454545454545455 = 6/11 (tag kt-cross1-u); no hits above 6/11.
- `results.jsonl`: one line per LP (word, extra atoms, Kakeya restriction on/off, size, value).
- `cert_kt-base.json`: the exact Katz-Tao certificate (6/11), accepted by `kakeya_cert_check.py` (self-test).

Verdict: H0 PASS, H1 NO, H2 NO. No certificate above 6/11 exists among these 4,524 configurations
of at most 14 atoms. No human mathematician has checked this.
