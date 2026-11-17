"""Additive maps never beat Theorem 1 (note a157, Theorem 34).

By MV2 of Munim, Inc., 2026-11-17. Researched and written with AI agents working in MV2's name.
No human mathematician has checked this. Code Apache-2.0.

Let q = p^m and let P : F_q^k -> F_q^k be F_p-linear (additive). For t in F_q put
n_t = dim_{F_p} ker(P + t), where t acts as scalar multiplication. Every map x -> P(x) + t x is
then F_p-linear, so its fibres are cosets of ker(P + t) and

    S(P) = q^k * log2(p) * sum_t n_t.

Theorem 34 says sum_t n_t <= k (q - 1)/(p - 1). So S(P) <= k (q - 1) q^k * log2(p)/(p - 1), which is
at most the improvement threshold k (q - 1) q^k, with equality possible only for p = 2: additive
maps (and, since constants do not change S, additive-plus-constant maps) never beat Theorem 1.
The coordinatewise Frobenius x -> x^p attains sum_t n_t = k (q - 1)/(p - 1) for every q.

This module checks the theorem by exhaustive enumeration of all F_p-linear maps for small (q, k),
by random samples for larger ones, and recomputes S(P) directly from the fibres.
It is self-contained (standard library only); the field moduli are the same as kakeya_entropy.py.

    python additive_maps.py --out-dir out
"""
import argparse
import itertools
import json
import math
import os
import random
import time

# Monic irreducible polynomials, coefficients from degree 0 up (same table as kakeya_entropy.py).
MODULI = {4: (2, (1, 1, 1)), 8: (2, (1, 1, 0, 1)), 9: (3, (1, 0, 1)), 16: (2, (1, 1, 0, 0, 1)),
          25: (5, (2, 1, 1)), 27: (3, (1, 2, 0, 1))}
PRIMES = (2, 3, 5, 7, 11, 13)


class SmallField:
    """F_q as the integers 0..q-1 (base-p digits = polynomial coefficients), with a mul table."""

    def __init__(self, q):
        if q in MODULI:
            p, mod = MODULI[q]
            m = len(mod) - 1
        elif q in PRIMES:
            p, mod, m = q, None, 1
        else:
            raise ValueError(f"unsupported field size {q}")
        self.q, self.p, self.m, self.mod = q, p, m, mod
        self.mul = [[self._mul(a, b) for b in range(q)] for a in range(q)]

    def digits(self, a):
        return [(a // self.p ** i) % self.p for i in range(self.m)]

    def number(self, ds):
        return sum(c * self.p ** i for i, c in enumerate(ds))

    def _mul(self, a, b):
        p, m = self.p, self.m
        if m == 1:
            return a * b % p
        prod = [0] * (2 * m - 1)
        for i, x in enumerate(self.digits(a)):
            for j, y in enumerate(self.digits(b)):
                prod[i + j] = (prod[i + j] + x * y) % p
        for deg in range(2 * m - 2, m - 1, -1):
            c = prod[deg]
            if c:
                for i, coeff in enumerate(self.mod):
                    prod[deg - m + i] = (prod[deg - m + i] - c * coeff) % p
        return self.number(prod[:m])

    def power(self, a, e):
        r = 1
        for _ in range(e):
            r = self.mul[r][a]
        return r


def block_diag(B, k):
    """k copies of the m x m block B on the diagonal (coordinate c uses rows c*m .. c*m+m-1)."""
    m = len(B)
    N = m * k
    M = [[0] * N for _ in range(N)]
    for c in range(k):
        for i in range(m):
            for j in range(m):
                M[c * m + i][c * m + j] = B[i][j]
    return M


def mult_block(F, t):
    """m x m matrix over F_p of x -> t x on F_q in the basis 1, X, ..., X^(m-1)."""
    cols = [F.digits(F.mul[t][F.p ** j]) for j in range(F.m)]
    return [[cols[j][i] for j in range(F.m)] for i in range(F.m)]


def frobenius_block(F):
    """m x m matrix over F_p of x -> x^p on F_q."""
    cols = [F.digits(F.power(F.p ** j, F.p)) for j in range(F.m)]
    return [[cols[j][i] for j in range(F.m)] for i in range(F.m)]


def scalar_matrices(F, k):
    return [block_diag(mult_block(F, t), k) for t in range(F.q)]


def frobenius_matrix(F, k):
    return block_diag(frobenius_block(F), k)


def rank_mod_p(M, p):
    rows = [list(r) for r in M]
    if not rows:
        return 0
    ncols = len(rows[0])
    rank = 0
    for c in range(ncols):
        piv = None
        for r in range(rank, len(rows)):
            if rows[r][c] % p:
                piv = r
                break
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        inv = pow(rows[rank][c], p - 2, p)
        rows[rank] = [(v * inv) % p for v in rows[rank]]
        for r in range(len(rows)):
            if r != rank and rows[r][c] % p:
                f = rows[r][c]
                rows[r] = [(a - f * b) % p for a, b in zip(rows[r], rows[rank])]
        rank += 1
        if rank == len(rows):
            break
    return rank


def kernel_dims(P, Ts, p):
    """[dim_{F_p} ker(P + T_t) for t in F_q]."""
    N = len(P)
    out = []
    for T in Ts:
        A = [[(P[i][j] + T[i][j]) % p for j in range(N)] for i in range(N)]
        out.append(N - rank_mod_p(A, p))
    return out


def bound(q, p, k):
    """k (q - 1)/(p - 1) = k (1 + p + ... + p^(m-1)), an integer."""
    return k * (q - 1) // (p - 1)


def threshold(q, k):
    """Improvement threshold of Corollary 1: S(P) > k (q - 1) q^k beats Theorem 1."""
    return k * (q - 1) * q ** k


def score_by_fibres(P, Ts, p):
    """S(P) = sum over t and over the fibres of x -> (P + T_t) x of s log2 s, by enumeration."""
    N = len(P)
    total = 0.0
    for T in Ts:
        A = [[(P[i][j] + T[i][j]) % p for j in range(N)] for i in range(N)]
        counts = {}
        for v in itertools.product(range(p), repeat=N):
            w = tuple(sum(A[i][j] * v[j] for j in range(N)) % p for i in range(N))
            counts[w] = counts.get(w, 0) + 1
        total += sum(c * math.log2(c) for c in counts.values() if c > 1)
    return total


def score_formula(q, k, p, dims):
    return q ** k * math.log2(p) * sum(dims)


def all_matrices(p, N):
    for entries in itertools.product(range(p), repeat=N * N):
        yield [list(entries[r * N:(r + 1) * N]) for r in range(N)]


def random_matrix(p, N, rng):
    return [[rng.randrange(p) for _ in range(N)] for _ in range(N)]


def census(q, k):
    """Exhaustive: every F_p-linear map on F_q^k. Returns the histogram of sum_t n_t."""
    F = SmallField(q)
    p, N = F.p, F.m * k
    Ts = scalar_matrices(F, k)
    hist = {}
    started = time.time()
    for P in all_matrices(p, N):
        s = sum(kernel_dims(P, Ts, p))
        hist[s] = hist.get(s, 0) + 1
    top = max(hist)
    return {"q": q, "k": k, "p": p, "mode": "exhaustive", "maps": p ** (N * N),
            "bound": bound(q, p, k), "max_sum": top, "maps_at_max": hist[top],
            "histogram": {str(s): hist[s] for s in sorted(hist)},
            "max_S": score_formula(q, k, p, [top]), "threshold": threshold(q, k),
            "holds": top <= bound(q, p, k), "seconds": round(time.time() - started, 1)}


def sample(q, k, count, seed=1):
    F = SmallField(q)
    p, N = F.p, F.m * k
    Ts = scalar_matrices(F, k)
    rng = random.Random(seed)
    top = -1
    worst = None
    for _ in range(count):
        P = random_matrix(p, N, rng)
        s = sum(kernel_dims(P, Ts, p))
        if s > top:
            top, worst = s, P
    frob = sum(kernel_dims(frobenius_matrix(F, k), Ts, p))
    return {"q": q, "k": k, "p": p, "mode": "sample", "maps": count, "seed": seed,
            "bound": bound(q, p, k), "max_sum": top, "frobenius_sum": frob,
            "holds": top <= bound(q, p, k) and frob <= bound(q, p, k), "example_at_max": worst}


EXHAUSTIVE = [(2, 2), (2, 3), (3, 2), (5, 2), (3, 3), (4, 1), (8, 1), (9, 1), (16, 1), (25, 1),
              (27, 1), (4, 2)]
SAMPLED = [(4, 3, 3000), (8, 2, 2000), (9, 2, 2000), (16, 2, 300), (27, 2, 200), (4, 4, 300),
           (25, 2, 200)]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--seed", type=int, default=1)
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    results = []
    path = os.path.join(args.out_dir, "additive_maps.json")
    for q, k in EXHAUSTIVE:
        results.append(census(q, k))
        print(json.dumps({key: results[-1][key] for key in results[-1] if key != "histogram"}))
        with open(path, "w") as fh:
            json.dump(results, fh, indent=1)
    for i, (q, k, count) in enumerate(SAMPLED):
        results.append(sample(q, k, count, seed=args.seed + i))
        print(json.dumps({key: results[-1][key] for key in results[-1]
                          if key != "example_at_max"}))
        with open(path, "w") as fh:
            json.dump(results, fh, indent=1)
    ok = all(r["holds"] for r in results)
    print("THEOREM_34_CHECK", "OK" if ok else "FAILED")


if __name__ == "__main__":
    main()
