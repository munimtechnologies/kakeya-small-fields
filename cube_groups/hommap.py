"""Exact check of the linear-algebra step behind Theorem 40 (robust-cubes-v6, run 42).

Lemma. Let V = Hom(F_2^a, F_2^b) and lam : V -> F_2^a linear with M lam(M) = 0 for every M in V.
If b >= 2 then lam = 0. If b = 1 the solutions are the symmetric zero-diagonal a x a matrices
(a(a-1)/2 dimensions), so the lemma needs b >= 2.

Two independent computations: (1) the linear system on a basis plus its polar form, solved by
Gaussian elimination over F_2; (2) brute force over every linear lam, testing M lam(M) = 0 for
EVERY M in V (no polarisation used). Pure Python, no dependencies.

Usage: python hommap.py [--out-dir DIR]
"""
import argparse
import itertools
import json
import os


def rank_f2(rows):
    """Rank of a list of int bitmasks over F_2."""
    pivots = {}
    r = 0
    for row in rows:
        x = row
        while x:
            hb = x.bit_length() - 1
            if hb in pivots:
                x ^= pivots[hb]
            else:
                pivots[hb] = x
                r += 1
                break
    return r


def var(m, i, a):
    """Index of unknown lam(E_m)_i."""
    return m * a + i


def basis(a, b):
    """Basis E_(p,q) of Hom(F_2^a, F_2^b): 1 at row p, column q."""
    return [(p, q) for p in range(b) for q in range(a)]


def nullity_linear(a, b):
    """Dimension of {lam : M lam(M) = 0 for all M}, via basis + polar equations."""
    E = basis(a, b)
    n = len(E) * a
    rows = []
    # E_(p,q) w = w_q e_p.
    for m, (p, q) in enumerate(E):
        rows.append(1 << var(m, q, a))                        # diagonal: lam(E_m)_q = 0
    for m, m2 in itertools.combinations(range(len(E)), 2):
        (p, q), (p2, q2) = E[m], E[m2]
        for c in range(b):                                    # E_m lam(E_m2) + E_m2 lam(E_m)
            row = 0
            if c == p:
                row ^= 1 << var(m2, q, a)
            if c == p2:
                row ^= 1 << var(m, q2, a)
            if row:
                rows.append(row)
    return n - rank_f2(rows)


def apply(M, w, a, b):
    """M (tuple of b row-bitmasks over a columns) applied to w (bitmask of length a)."""
    out = 0
    for p in range(b):
        if bin(M[p] & w).count("1") & 1:
            out |= 1 << p
    return out


def all_maps(a, b):
    return list(itertools.product(range(1 << a), repeat=b))


def count_brute(a, b):
    """Number of linear lam with M lam(M) = 0 for every M in V (brute force)."""
    E = basis(a, b)
    d = len(E)
    Ms = all_maps(a, b)
    # coordinates of each M in the basis E
    coords = []
    for M in Ms:
        c = 0
        for m, (p, q) in enumerate(E):
            if (M[p] >> q) & 1:
                c |= 1 << m
        coords.append(c)
    count = 0
    for lam in itertools.product(range(1 << a), repeat=d):   # lam(E_m) for each m
        ok = True
        for M, c in zip(Ms, coords):
            w = 0
            for m in range(d):
                if (c >> m) & 1:
                    w ^= lam[m]
            if apply(M, w, a, b):
                ok = False
                break
        if ok:
            count += 1
    return count


def predicted_nullity(a, b):
    return 0 if b >= 2 else a * (a - 1) // 2


def theorem40_bound(a, b, s):
    """Upper bound on n = rank(L/A) from Theorems 39 and 40 (b >= 2 uses Theorem 40 at s = 0)."""
    t39 = a + 2 * b + a * b - s * (b - 1)
    if b >= 2 and s == 0:
        return t39 - 1
    return t39


def settled(a, b):
    """True if n <= 2a + 3b (|L| <= |Omega_1|^4) for every s in 0..a, or trivially by n <= ak."""
    need = 2 * a + 3 * b
    if a * (a + b) <= need:
        return True
    return all(theorem40_bound(a, b, s) <= need for s in range(a + 1))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    out = {"linear": {}, "brute": {}, "settled_table": {}}
    for a in range(1, 6):
        for b in range(1, 5):
            nl = nullity_linear(a, b)
            out["linear"][f"{a},{b}"] = nl
            print(f"linear a={a} b={b}: nullity {nl}, predicted {predicted_nullity(a, b)}, "
                  f"match {nl == predicted_nullity(a, b)}")
    for a, b in [(1, 1), (2, 1), (3, 1), (1, 2), (2, 2), (3, 2), (2, 3), (1, 3)]:
        c = count_brute(a, b)
        out["brute"][f"{a},{b}"] = c
        print(f"brute a={a} b={b}: solutions {c}, predicted {2 ** predicted_nullity(a, b)}, "
              f"match {c == 2 ** predicted_nullity(a, b)}")
    for a in range(1, 8):
        row = []
        for b in range(0, 6):
            st = settled(a, b) if b > 0 else True
            row.append("Y" if st else ".")
            out["settled_table"][f"{a},{b}"] = st
        print(f"settled a={a}: b=0..5 " + " ".join(row))
    ok = all(out["linear"][k] == predicted_nullity(*map(int, k.split(","))) for k in out["linear"])
    ok = ok and all(out["brute"][k] == 2 ** predicted_nullity(*map(int, k.split(",")))
                    for k in out["brute"])
    out["all_match"] = ok
    print(f"SUMMARY all_match {ok}, (3,2) settled {settled(3, 2)}, (4,2) settled {settled(4, 2)}, "
          f"(3,3) settled {settled(3, 3)}")
    os.makedirs(args.out_dir, exist_ok=True)
    with open(os.path.join(args.out_dir, "hommap.json"), "w") as f:
        json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
