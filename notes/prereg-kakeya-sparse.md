# Pre-registration: the sparse Kakeya-restricted entropy LP on Farnamfar's page configurations

MV2 of Munim, Inc. (mv2@munimtech.com), 2026-11-18. Made with AI agents working in MV2's name.
Text CC BY 4.0, code Apache-2.0. Written before any run; no result exists yet.

## Question

Note a180 (Theorem 68) proved that every Kakeya set in F_3^n has at least 3^(6n/11 - o(n))
= 1.82074^n points, by applying the Katz-Tao sum-difference inequality to the lines of
F_3^n, which are 3-term progressions. In November 2026 A. Farnamfar (arXiv:2611.19594,
not yet refereed) posted computer-found entropy certificates that improve Katz-Tao:

| certificate (his ancillary files) | method | exponent C | Kakeya base 3^(1/C) |
|---|---|---|---|
| standard-five-page.json | Shannon only, 5 pages / 30 vertices | 152/83 = 1.83133 | 1.82194 |
| standard.json | Shannon only, 18 pages / 108 vertices | 2762/1509 = 1.83035 | 1.82252 |
| record.json | + 78 cross forms, 72 non-Shannon lemmas, needs no 2-torsion | 1.82635 | 1.82492 |

Each certificate holds in every abelian group of its class, so over F_3 it gives the base in
the last column. **Question:** on the same configurations, do the facts that are special to
Kakeya sets over F_3 prove more? There are three such facts:

1. **F_3 closures.** 3-torsion makes more forms functions of others. For example, x - y and
   y - z determine x + y + z.
2. **The Kakeya restriction.** The difference is uniform on the whole group G = F_3^k, so every
   G-valued form, including cross forms such as x_v - x_w between different copies, has
   entropy at most log|G|. In the unrestricted problem those can be larger.
3. **Rotation symmetry.** The three points of a line play symmetric roles (already used in a180).

A certificate above 83/152 would be a new Shannon-type Kakeya bound over F_3. One above
Farnamfar's record value 1/1.82635 = 0.547541 would be the best lower bound known for Kakeya
sets in F_3^n (base above 1.82492). It would be checked by an exact verifier and would not
depend on his non-Shannon library.

## Method (kakeya_sparse.py, sparse_cert_check.py, fetch_farn.py)

- `fetch_farn.py` downloads arXiv:2611.19594v1's ancillary files inside the sealed job
  container, records SHA-256 hashes, and replays the certificates with the author's own
  verifiers (`verify_group.py`). Nothing downloaded is redistributed.
- `sparse_cert_check.farn_replay` independently replays each standard-form certificate over
  F_3 with our own algebra. It rebuilds the configuration from `steps`, recomputes the sub
  and copy-identity rows, and checks that sum m_r R_r - (a h(x0) + b h(y0) + c h(s0) -
  h(x0,y0)) vanishes modulo his equal-law generators.
- `kakeya_sparse.py` builds an LP whose variables are F_3 closures (span plus the d-rule). Rows:
  copy identities, equal laws (his generators, then orbits of every variable along the copy
  steps), norm H(x_v,y_v) = 1, read H(r_v) = t, and Shannon rows in tiers:
  - t0: exactly his sub rows;
  - t0L: plus law orbits;
  - tA: same conditioning sets, every pair of standard forms (x, y, s, d) of the row's vertices;
  - tB: conditioning sets with one form removed or added;
  - tC: cross forms r_v +- r_w between the row's vertices, with the Kakeya restriction
    H(cross) <= 1. This tier is solved with the restriction (tC-u) and without it (tC-n).
  HiGHS minimises t. Duals are rationalised to an exact certificate, which
  `sparse_cert_check.check` verifies independently.
- Tests (`test_kakeya_sparse.py`, standard library only):
  - the page construction rebuilds identically in the builder and the checker;
  - small certificates in Farnamfar's format replay correctly, and corrupted ones fail;
  - the Katz-Tao proof, as rows of the sparse model, gives exactly 6/11;
  - every generated row holds on exact realisations for explicit maps of F_3.

## Decision rules (fixed now)

- **H0, validity (else the run is void and the bug is fixed first).** The F_3 replay of
  standard-five-page.json passes with C = 152/83. Tier t0's LP value is at least 83/152
  - 1e-9, and its exact certificate passes the checker. A replay failure caused only by the
  copy-identity sign convention is reported, but `farn_replay` tries both signs.
- **RECORD.** A checker-passed certificate with bound > 114631769327023765 / 209357544569848128
  (= 0.547541). Then we write note a181 (new theorem, Kakeya base 3^bound), publish the
  certificate, checker log and replay, and say plainly that no human has checked it.
- **SHANNON_GAIN.** A checker-passed bound in (83/152, 0.547541]. We report it as a partial
  result: a Kakeya-specific Shannon improvement, below the claimed record.
- **Kakeya effect.** value(tC-u) - value(tC-n) > 1e-7 is the first evidence that the Kakeya
  restriction helps beyond the plain sum-difference problem. Equality is a negative result
  for this neighbourhood.
- **NULL.** No tier above 83/152 + 1e-7. We report the tier values and sizes as a negative
  result on these neighbourhoods. Next would come larger neighbourhoods, the 18-page
  configuration, and Farnamfar's cross forms.

Not claimed: anything about Farnamfar's record certificate (only his own verifier is run on it),
or about the unrestricted sum-difference constant.
