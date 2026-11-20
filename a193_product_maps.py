# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name; no human has checked this.
"""Checks for note a193 (Proposition 87 and Observation 87.1). Standard library only.

Proposition 87: the quadratic maps P: F_3^3 -> F_3^3 with P(0) = 0 and S(P) = 162 are exactly
the "product maps" P = B o (p_1 x p_2 x p_3) o B^{-1}, p_j(y) = a_j y^2 + lam_j y, a_j != 0.
This script enumerates every product map from (frame, signs, linear diagonal), checks that the
234 * 8 * 27 = 50,544 parameter choices give 50,544 DISTINCT maps (the count a192's exhaustive
scan found for equality), that each has S = 162, and that the number with a given linear part
DP(0) = L matches a192's per-class table (1872 for L = 0 or I, 48 for diag(1,0,0), 8 for diag(0,1,2)).

Observation 87.1: the triangular map G(x) = (x1^2, -x1 x2, x3^2 - x1 x3 + 1) is a full sticky
tree of height 3 with slices of sizes (8, 8, 8) and column profile (2, 6) in every slice,
unlike the classical tree (4, 4).

Usage: python a193_product_maps.py [out.json]
"""
import itertools
import json
import math
import sys

VECS = list(itertools.product(range(3), repeat=3))
IDX = {v: i for i, v in enumerate(VECS)}


def lines():
    """The 13 lines of F_3^3, each by its representative with first nonzero coordinate 1."""
    out = []
    for v in VECS:
        if v == (0, 0, 0):
            continue
        first = next(c for c in v if c)
        if first == 1:
            out.append(v)
    return out


def det3(a, b, c):
    """Determinant mod 3 of the matrix with columns a, b, c: a . (b x c)."""
    cross = (b[1] * c[2] - b[2] * c[1], b[2] * c[0] - b[0] * c[2], b[0] * c[1] - b[1] * c[0])
    return (a[0] * cross[0] + a[1] * cross[1] + a[2] * cross[2]) % 3


def frames():
    """Unordered triples of independent lines (expected 11232 / (8 * 6) = 234)."""
    return [f for f in itertools.combinations(lines(), 3) if det3(*f) != 0]


def combine(B, y):
    """x = y_0 b_0 + y_1 b_1 + y_2 b_2 (mod 3)."""
    return tuple((B[0][i] * y[0] + B[1][i] * y[1] + B[2][i] * y[2]) % 3 for i in range(3))


def product_map(B, a, lam):
    """Value table (in VECS order) of x -> B p(B^{-1} x), p_j(y) = a_j y^2 + lam_j y."""
    table = {}
    for y in VECS:
        py = tuple((a[j] * y[j] * y[j] + lam[j] * y[j]) % 3 for j in range(3))
        table[combine(B, y)] = combine(B, py)
    assert len(table) == 27
    return tuple(table[x] for x in VECS)


def s_value(vals):
    """S(P) = sum_t sum_{fibres F of x -> P(x) + t x} |F| log2 |F|."""
    s = 0.0
    for t in range(3):
        counts = {}
        for x, px in zip(VECS, vals):
            key = ((px[0] + t * x[0]) % 3, (px[1] + t * x[1]) % 3, (px[2] + t * x[2]) % 3)
            counts[key] = counts.get(key, 0) + 1
        s += sum(c * math.log2(c) for c in counts.values() if c > 1)
    return s


def linear_part(vals):
    """Rows of L = DP(0). For P = Q + L (Q homogeneous quadratic), L x = 2 (P(x) - P(-x)) mod 3."""
    cols = []
    for i in range(3):
        e = tuple(1 if j == i else 0 for j in range(3))
        me = tuple((-c) % 3 for c in e)
        pe, pme = vals[IDX[e]], vals[IDX[me]]
        cols.append(tuple((2 * (pe[k] - pme[k])) % 3 for k in range(3)))
    return tuple(tuple(cols[j][i] for j in range(3)) for i in range(3))


def diag(d0, d1, d2):
    return ((d0, 0, 0), (0, d1, 0), (0, 0, d2))


def sticky_G(x):
    x1, x2, x3 = x
    return ((x1 * x1) % 3, (-x1 * x2) % 3, (x3 * x3 - x1 * x3 + 1) % 3)


def classical_G(x):
    return tuple((c * c) % 3 for c in x)


def slices(G):
    out = []
    for t in range(3):
        out.append({tuple((g + t * xi) % 3 for g, xi in zip(G(x), x)) for x in VECS})
    return out


def column_profile(S):
    cols = {}
    for p in S:
        cols[p[0]] = cols.get(p[0], 0) + 1
    return sorted(cols.values())


def run():
    fr = frames()
    maps = {}
    for B in fr:
        for a in itertools.product((1, 2), repeat=3):
            for lam in VECS:
                vals = product_map(B, a, lam)
                maps[vals] = maps.get(vals, 0) + 1
    s_ok = 0
    s_values = set()
    zero_at_zero = 0
    per_L = {}
    for vals in maps:
        s = s_value(vals)
        s_values.add(round(s, 9))
        if abs(s - 162.0) < 1e-9:
            s_ok += 1
        if vals[IDX[(0, 0, 0)]] == (0, 0, 0):
            zero_at_zero += 1
        L = linear_part(vals)
        per_L[L] = per_L.get(L, 0) + 1
    reps = {
        "L=0": diag(0, 0, 0),
        "L=I": diag(1, 1, 1),
        "L=diag(1,0,0)": diag(1, 0, 0),
        "L=diag(2,0,0)": diag(2, 0, 0),
        "L=diag(0,1,2)": diag(0, 1, 2),
        "L=[[1,1,0],[0,1,0],[0,0,0]] (not diagonalisable)": ((1, 1, 0), (0, 1, 0), (0, 0, 0)),
    }
    sticky = slices(sticky_G)
    classical = slices(classical_G)
    return {
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "lines": len(lines()),
        "frames": len(fr),
        "parameter_choices": len(fr) * 8 * 27,
        "distinct_maps": len(maps),
        "max_multiplicity": max(maps.values()),
        "maps_with_S_162": s_ok,
        "S_values": sorted(s_values),
        "maps_with_P0_zero": zero_at_zero,
        "distinct_linear_parts": len(per_L),
        "per_L": {k: per_L.get(v, 0) for k, v in reps.items()},
        "sticky_G_slice_sizes": [len(S) for S in sticky],
        "sticky_G_column_profiles": [column_profile(S) for S in sticky],
        "classical_slice_sizes": [len(S) for S in classical],
        "classical_column_profiles": [column_profile(S) for S in classical],
    }


if __name__ == "__main__":
    res = run()
    text = json.dumps(res, indent=1)
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as fh:
            fh.write(text + "\n")
    print(text)
