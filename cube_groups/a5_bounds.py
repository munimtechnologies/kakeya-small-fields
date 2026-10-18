# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""A(5) = 5 (notes/a5.md): the finite step of Lemma 52, the table of Corollary 26 and the settled
cases of Corollary 27.

core: the proof of Lemma 52 ends in a statement about 3 x 3 matrices over F_2 (R = Im A_u has
dimension 3, and P_h is the restriction of A_h to R, of rank <= 1). Checked here over every matrix of
rank <= 1:

    (d = 1) if a = P1 + P2 has rank 2 and kernel span(z), there is no z' outside span(z) with
            P1 z' = 0 and P2 (z + z') = 0;
    (d = 2) if a = P1 + P2 = P3 + P4 has rank 1 and kills two independent vectors x0 and z, then
            P1 x0 = P2 x0 = x0 and P3 x0 = P4 x0 = x0 + z cannot all hold.

The control repeats both counts with rank <= 2 in place of rank <= 1; there solutions exist, so the
counts can fail.

table: the bounds of Proposition 24 (notes/rank-restriction.md) recomputed with A(5) = 5, and the
count of Corollary 17 with these bounds. With known=4 it gives the old table.

Matrices are 9-bit masks with entry (r, c) at bit 3 r + c (0-based), vectors 3-bit masks. Pure
Python, no dependencies.

Usage: python a5_bounds.py [--out-dir DIR]
"""
import argparse
import json
import os


def parity(x):
    return bin(x).count("1") & 1


def apply3(P, x):
    y = 0
    for r in range(3):
        if parity((P >> (3 * r)) & 7 & x):
            y |= 1 << r
    return y


def rank_rows(rows, width):
    rows = list(rows)
    rank = 0
    for bit in range(width):
        piv = next((i for i in range(rank, len(rows)) if rows[i] >> bit & 1), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        for i in range(len(rows)):
            if i != rank and rows[i] >> bit & 1:
                rows[i] ^= rows[rank]
        rank += 1
    return rank


RANK3 = [rank_rows([(P >> (3 * r)) & 7 for r in range(3)], 3) for P in range(512)]


def kernel(P):
    """The non-zero vectors that P kills."""
    return [x for x in range(1, 8) if apply3(P, x) == 0]


# ---------- the finite step of Lemma 52 ----------

def core_d1(max_rank=1):
    """(pairs (P1, P2) with rank <= max_rank and rank(P1 + P2) = 2, number of (P1, P2, z') with
    z' not in {0, z}, P1 z' = 0 and P2 (z + z') = 0, where span(z) = ker(P1 + P2))."""
    small = [P for P in range(512) if RANK3[P] <= max_rank]
    cases = found = 0
    for P1 in small:
        for P2 in small:
            a = P1 ^ P2
            if RANK3[a] != 2:
                continue
            cases += 1
            z = kernel(a)[0]
            for zp in range(1, 8):
                if zp != z and apply3(P1, zp) == 0 and apply3(P2, zp ^ z) == 0:
                    found += 1
    return cases, found


def core_d2(max_rank=1):
    """(triples (a, x0, z) with rank a = 1 and x0 != z non-zero in ker a, number of them for which
    a = P1 + P2 = P3 + P4 with every P_i of rank <= max_rank, P1 x0 = P2 x0 = x0 and
    P3 x0 = P4 x0 = x0 + z)."""
    small = set(P for P in range(512) if RANK3[P] <= max_rank)
    cases = found = 0
    for a in range(512):
        if RANK3[a] != 1:
            continue
        pairs = [(P, P ^ a) for P in small if P ^ a in small]
        for x0 in kernel(a):
            for z in kernel(a):
                if z == x0:
                    continue
                cases += 1
                first = any(apply3(P, x0) == x0 and apply3(Q, x0) == x0 for P, Q in pairs)
                second = any(apply3(P, x0) == x0 ^ z and apply3(Q, x0) == x0 ^ z for P, Q in pairs)
                if first and second:
                    found += 1
    return cases, found


# ---------- Corollaries 26 and 27 ----------

def bounds(tmax, known=5):
    """Upper bounds A[t] >= A(t) and E[t] >= M(t) - t for t = 0..tmax: A(t) = t for t <= known
    (Theorems 26 and 27), and for t > known the recursion of Proposition 24,
    A(t) <= min(2t, max(t, t + A(t - 4), max over 0 < d < t of M(t - d) + A(d))),
    with M(s) <= s + E(s) and E(s) = max over r <= s of (A(r) - r) (Theorem 24)."""
    A, E = [0], [0]
    for t in range(1, max(tmax, known) + 1):
        if t <= known:
            A.append(t)
        else:
            red = max(t - d + E[t - d] + A[d] for d in range(1, t))
            A.append(min(2 * t, max(t, t + A[t - 4], red)))
        E.append(max(E[t - 1], A[t] - t))
    return A[:tmax + 1], E[:tmax + 1]


def settled(a, b, known=5):
    """The count of Corollary 14 with these bounds: tau = the largest t <= a with E[s] <= b for
    every s <= t; the pair (a, b) is settled if (a - tau - 2)(b - 1) <= 1."""
    if b <= 1:
        return True
    E = bounds(a, known)[1]
    tau = 0
    while tau < a and E[tau + 1] <= b:
        tau += 1
    return (a - tau - 2) * (b - 1) <= 1


EXTRA17 = {(10, 4), (10, 5), (10, 6), (11, 6), (10, 7), (11, 7), (11, 8), (12, 8), (12, 9),
           (13, 10)}
EXTRA27 = EXTRA17 | {(11, 5)}


def table():
    A, E = bounds(14)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    old = {(a, b): settled(a, b, known=4) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "newly_settled": sorted(k for k in grid if grid[k] and not old[k]),
            "graded": {"a_bounds": A[:13] == [0, 1, 2, 3, 4, 5, 8, 10, 12, 14, 18, 21, 24],
                       "e_bounds": E[:13] == [0, 0, 0, 0, 0, 0, 2, 3, 4, 5, 8, 10, 12],
                       "old_table": bounds(12, known=4) == (
                           [0, 1, 2, 3, 4, 6, 8, 10, 12, 15, 18, 21, 24],
                           [0, 0, 0, 0, 0, 1, 2, 3, 4, 6, 8, 10, 12]),
                       "corollary27": all(v == (b <= 1 or a <= max(9, b + 2) or (a, b) in EXTRA27)
                                          for (a, b), v in grid.items()),
                       "contains_corollary17": all(v for (a, b), v in grid.items() if old[(a, b)])}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="")
    args = ap.parse_args()
    out = {"core": {"d1": core_d1(1), "d2": core_d2(1)},
           "control": {"d1": core_d1(2), "d2": core_d2(2)},
           "table": table()}
    text = json.dumps(out, indent=1)
    print(text)
    if args.out_dir:
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "a5.json"), "w") as f:
            f.write(text)


if __name__ == "__main__":
    main()
