# K(3, 4) = 28: every Kakeya set in F_4^3 has at least 28 points (computer-assisted)

Made with AI agents working in MV2's name (MV2 of Munim, Inc., mv2@munimtech.com).
**Not checked by a human mathematician.** Text CC BY 4.0, code Apache-2.0.

This file is committed only together with `results/progress-q4-T28.json` and only if
`test_k34_complete.py` passes on it, that is, only if the search of PROOF.md finished every
subproblem and found no Kakeya set of F_4^3 with 27 or fewer points.

## Statement

The smallest Kakeya set in F_4^3 has exactly 28 points. The upper bound is the even-q
construction of Kopparty, Saraf and Sudan (16 + 12 points; `verify.kss_set_q4`). The lower
bound is the exhaustive slice search of PROOF.md: for every r <= 6 and every one of the 21
orbit representatives S_0 of r-point subsets of AG(2, 4) under AGL(2, 4) x Frobenius, every map
f from the 16 transversal directions onto S_0 (with f(0) = S_0[0]) was either pruned by the
bound |K| >= r + sum max(|S_c| + ceil(N_c / r), r) >= 28 or completed and given its exact best
horizontal placement, which was never below 28.

Before this, the best bounds were 21 <= K(3, 4) <= 28 (Bukh and Chao, arXiv:2108.00074; KSS).
Lund, Saraf and Wolf (arXiv:1609.01048) note that exact Kakeya numbers were known only in the
plane. Our earlier search gave K(3, 3) = 13; this would be the first exact value in three
dimensions over a field with more than three elements.

## What backs it

* The hand reduction in PROOF.md (smallest plane, at most 6 points; transversal map f; shear
  and AGL(2, 4) x Frobenius symmetry; exact leaf placement).
* Controls in test_k34_unit.py: the same code over F_3 reproduces K(3, 3) = 13 (none below 13,
  13-point sets found and confirmed by the separate checker verify.py); field and group checks;
  the KSS set evaluated through the leaf code gives 28.
* Positive control in F_4 (results/control-q4-T29.json): asked for sets below 29 on the orbit of
  the 2 x 2 slice, the search reaches a 28-point set, which the checker confirms.
* Per-item counts (nodes, leaves, leaf minima, histograms) are in results/progress-q4-T28.json.

## Limits

A computer proof is only as good as the reduction and the code. The reduction is a short hand
argument that no human mathematician has checked. A second, independently written search (k34b/)
is running to re-check the code path; until it finishes, treat this as one computer route.
