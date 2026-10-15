"""Kakeya sets of higher rank over a fixed finite field (README section 10).

A rank-r Kakeya set in F_q^n contains a translate of every r-dimensional subspace, and
beta_(q,r) = lim K_r(n, q)^(1/n) is the growth base of the smallest ones. For f : F_q^r -> F_q let

    Phi(f) = (1/q^r) * sum over t in F_q^r of H(f(U) + <t, U>),    U uniform on F_q^r.

Theorem 5: beta_(q,r) <= 2^Phi(f) for every f. This module has small finite fields, the three
witnesses of Corollary 4 (f = 0, the square of one coordinate, the norm form of F_(q^2) on two
coordinates), their closed forms, the bounds of Kopparty, Lev, Saraf and Sudan (KLSS) to compare
with, the finite check of Theorem 5 on every plane of a small space, and an exhaustive search over
every f for small q and r.

  python higher_rank.py table                bases for r = 2, 3, 4
  python higher_rank.py search --q 3 --r 2   every f : F_3^2 -> F_3

By MV2 of Munim, Inc., 2026-10-15. Researched and written with AI agents working in MV2's name.
Code Apache-2.0.
"""
import argparse
import json
import math
from itertools import product

# q = p^e with e > 1: (p, e, coefficients of a monic irreducible polynomial, lowest degree first)
EXTENSIONS = {4: (2, 2, [1, 1, 1]), 8: (2, 3, [1, 1, 0, 1]), 9: (3, 2, [1, 0, 1]),
              16: (2, 4, [1, 1, 0, 0, 1])}
FIELD_SIZES = [2, 3, 4, 5, 7, 8, 9, 11, 13, 16]


def is_prime(n):
    return n >= 2 and all(n % d for d in range(2, int(n ** 0.5) + 1))


class Field:
    """F_q on the integers 0..q-1; the base-p digits of an element are polynomial coefficients."""

    def __init__(self, q):
        if is_prime(q):
            p, e, modulus = q, 1, [0, 1]
        elif q in EXTENSIONS:
            p, e, modulus = EXTENSIONS[q]
        else:
            raise ValueError(f"unsupported field size {q}")
        self.q, self.p = q, p
        digits = [[(a // p ** i) % p for i in range(e)] for a in range(q)]

        def code(ds):
            return sum(d * p ** i for i, d in enumerate(ds))

        def times(a, b):
            prod = [0] * (2 * e - 1)
            for i, x in enumerate(digits[a]):
                for j, y in enumerate(digits[b]):
                    prod[i + j] = (prod[i + j] + x * y) % p
            for d in range(2 * e - 2, e - 1, -1):
                c = prod[d]
                if c:
                    for i, m in enumerate(modulus):
                        prod[d - e + i] = (prod[d - e + i] - c * m) % p
            return code(prod[:e])

        self.add = [[code([(x + y) % p for x, y in zip(digits[a], digits[b])]) for b in range(q)]
                    for a in range(q)]
        self.mul = [[times(a, b) for b in range(q)] for a in range(q)]
        self.neg = [self.add[a].index(0) for a in range(q)]

    def dot(self, t, u):
        s = 0
        for a, b in zip(t, u):
            s = self.add[s][self.mul[a][b]]
        return s

    def vectors(self, r):
        return list(product(range(self.q), repeat=r))

    def norm_coefficients(self):
        """(a, b) with t^2 + a t + b irreducible over F_q. Then N(x, y) = x^2 + a x y + b y^2 is the
        norm of x - y theta from F_(q^2), theta a root: it vanishes only at (0, 0)."""
        for a in range(self.q):
            for b in range(1, self.q):
                if all(self.add[self.add[self.mul[t][t]][self.mul[a][t]]][b] for t in range(self.q)):
                    return a, b
        raise AssertionError("no irreducible quadratic")


def zero_witness(F):
    return lambda u: 0


def square_witness(F):
    """f(u) = u_1^2: the witness of Theorem 1, on one coordinate."""
    return lambda u: F.mul[u[0]][u[0]]


def norm_witness(F):
    """f(u) = N(u_1, u_2), the norm form of F_(q^2) on the first two coordinates (r >= 2)."""
    a, b = F.norm_coefficients()

    def f(u):
        x, y = u[0], u[1]
        return F.add[F.add[F.mul[x][x]][F.mul[a][F.mul[x][y]]]][F.mul[b][F.mul[y][y]]]
    return f


def translate(F, f, b):
    """u -> f(u - b)."""
    minus_b = [F.neg[x] for x in b]
    return lambda u: f(tuple(F.add[x][y] for x, y in zip(u, minus_b)))


def entropy(counts):
    n = sum(counts)
    return math.log2(n) - sum(c * math.log2(c) for c in counts if c > 1) / n


def slice_counts(F, f, columns, t):
    """How often each symbol occurs among f(u) + <t, u>, u in `columns`."""
    counts = [0] * F.q
    for u in columns:
        counts[F.add[f(u)][F.dot(t, u)]] += 1
    return counts


def phi(F, r, f, columns=None):
    """(1/q^r) sum over t in F_q^r of H(f(U) + <t, U>), with U uniform on the list `columns`
    (repeats allowed; default: every vector of F_q^r)."""
    ts = F.vectors(r)
    columns = ts if columns is None else columns
    return sum(entropy(slice_counts(F, f, columns, t)) for t in ts) / len(ts)


def phi_zero(q, r):
    """f = 0: the slice t = 0 is constant and the others are uniform (KLSS Theorem 10's base)."""
    return (1 - q ** -r) * math.log2(q)


def phi_square(q, r):
    """f(u) = u_1^2: only the q slices with t_2 = ... = t_r = 0 are not uniform (Lemma 2)."""
    return math.log2(q) - (q - 1) / q ** r


def norm_deficit(q):
    """D(q) = q^2 log2(1 + 1/q) - log2(q + 1); the norm witness has Phi = log2 q - D(q) / q^r."""
    return q * q * math.log2(1 + 1 / q) - math.log2(q + 1)


def phi_norm(q, r):
    return math.log2(q) - norm_deficit(q) / q ** r


def phi_best(q, r):
    """The least Phi among the witnesses of Corollary 4."""
    values = [phi_zero(q, r), phi_square(q, r)]
    if r >= 2:
        values.append(phi_norm(q, r))
    return min(values)


def one_coordinate_floor(q, r):
    """No f has Phi below this (Proposition 1); 2 to this power is the KLSS Theorem 1 bound."""
    return math.log2(q) - math.log2(1 + (q - 1) / q ** r)


def klss_lower(q, r):
    """KLSS Theorem 1: beta_(q,r) >= q^(r+1) / (q^r + q - 1)."""
    return q ** (r + 1) / (q ** r + q - 1)


def klss_theorem10(q, r):
    return q ** (1 - q ** -r)


def klss_theorem4(q, r):
    delta = 1 if q % 2 == 0 else (5 / 3 if q == 3 else 3)
    return q * (1 - (q - delta) / (2 * q ** r)) ** (1 / (r + 1))


def klss_best(q, r):
    """The smaller of the two KLSS upper bounds on beta_(q,r) for fixed q and growing n."""
    return min(klss_theorem10(q, r), klss_theorem4(q, r))


def asymptotic_window(q, r):
    """Corollary 5 (r >= 2): q - q^(2-r) + q^(1-r) <= beta_(q,r)
    <= q - q^(2-r) + (1 + ln(q + 1)) q^(1-r)."""
    low = q - q ** (2 - r) + q ** (1 - r)
    high = q - q ** (2 - r) + (1 + math.log(q + 1)) * q ** (1 - r)
    return low, high


def planes(F, n):
    """One basis (x, y) for each 2-dimensional subspace of F_q^n."""
    found = {}
    for x in F.vectors(n):
        for y in F.vectors(n):
            span = frozenset(tuple(F.add[F.mul[a][xi]][F.mul[b][yi]] for xi, yi in zip(x, y))
                             for a in range(F.q) for b in range(F.q))
            if len(span) == F.q ** 2 and span not in found:
                found[span] = (x, y)
    return list(found.values())


def log2_class_size(z, q):
    """log2 of the number of vectors with the same symbol counts as z."""
    counts = [0] * q
    for a in z:
        counts[a] += 1
    size = math.factorial(len(z))
    for c in counts:
        size //= math.factorial(c)
    return math.log2(size)


def flat_cost(F, f, basis):
    """Average of log2 N(z) over the points z of the flat a + span(basis), where coordinate c of a
    is f(u_c) and u_c is the column of coordinate c in the basis (Theorem 5 with one block)."""
    n = len(basis[0])
    columns = [tuple(d[c] for d in basis) for c in range(n)]
    a = [f(u) for u in columns]
    points = F.vectors(len(basis))
    total = 0.0
    for t in points:
        total += log2_class_size([F.add[a[c]][F.dot(t, columns[c])] for c in range(n)], F.q)
    return total / len(points)


def search(q, r):
    """Every f : F_q^r -> F_q, as the tuple of its values on F.vectors(r). Returns the least Phi,
    how many f attain it and one of them; the least Phi among the f whose every slice takes all q
    values; the largest number of slices that miss a value; and whether every f with three or more
    such slices changes by a constant along some nonzero direction (Proposition 2)."""
    F = Field(q)
    vecs = F.vectors(r)
    N = len(vecs)
    index = {u: i for i, u in enumerate(vecs)}
    dots = [[F.dot(t, u) for u in vecs] for t in vecs]
    shift = [[index[tuple(F.add[x][y] for x, y in zip(u, w))] for u in vecs] for w in vecs]
    xlogx = [c * math.log2(c) if c > 1 else 0.0 for c in range(N + 1)]
    add, neg = F.add, F.neg
    best = best_full = None
    at_best, example, most_missing, one_direction = 0, None, 0, True
    for values in product(range(q), repeat=N):
        S = 0.0
        missing = 0
        for row in dots:
            counts = [0] * q
            for v, d in zip(values, row):
                counts[add[v][d]] += 1
            S += sum(xlogx[c] for c in counts)
            missing += 0 in counts
        value = r * math.log2(q) - S / (N * N)
        if best is None or value < best - 1e-12:
            best, at_best, example = value, 1, values
        elif value < best + 1e-12:
            at_best += 1
        if missing == 0 and (best_full is None or value < best_full):
            best_full = value
        most_missing = max(most_missing, missing)
        if missing >= 3 and one_direction:
            one_direction = any(
                len({add[values[shift[w][i]]][neg[values[i]]] for i in range(N)}) == 1
                for w in range(1, N))
    return {"q": q, "r": r, "functions": q ** N, "min_phi": best, "maps_at_min": at_best,
            "example": list(example), "min_phi_all_values": best_full,
            "most_missing_slices": most_missing,
            "three_missing_means_one_direction": one_direction}


def main():
    ap = argparse.ArgumentParser()
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("table")
    s = sub.add_parser("search")
    s.add_argument("--q", type=int, default=3)
    s.add_argument("--r", type=int, default=2)
    args = ap.parse_args()
    if args.cmd == "table":
        print("r   q   KLSS lower   best KLSS upper   Theorem 5")
        for r in (2, 3, 4):
            for q in FIELD_SIZES:
                print(f"{r}  {q:2d}   {klss_lower(q, r):10.4f}   {klss_best(q, r):15.4f}"
                      f"   {2 ** phi_best(q, r):9.4f}")
    else:
        print(json.dumps(search(args.q, args.r), indent=1))


if __name__ == "__main__":
    main()
