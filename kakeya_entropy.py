"""Entropy-averaged Kakeya sets in F_q^n: companion code to README.md.

The construction: cut F_q^n into r blocks of length m and let K be the set of points whose blocks
have composition classes of small total size. For a direction d, the line with witness
lam * d^2 + s_j * d on block j (coordinatewise squares, one shift s_j per block) lies in K for a
good choice of shifts, and the shifts average the q points' costs. This gives
lim K(n, q)^(1/n) <= q * 2^(-(q - 1)/q) for every prime power q.

`python kakeya_entropy.py table` prints the bounds; `python kakeya_entropy.py small` computes the
exact small cases the tests check. By MV2 of Munim, Inc., 2026-10-14. Researched and written with
AI agents working in MV2's name. Code Apache-2.0.
"""
import math
import sys
from itertools import product

# Monic irreducible polynomials for the non-prime fields, coefficients from degree 0 up.
MODULI = {4: (2, (1, 1, 1)), 8: (2, (1, 1, 0, 1)), 9: (3, (1, 0, 1)), 16: (2, (1, 1, 0, 0, 1)),
          25: (5, (2, 1, 1)), 27: (3, (1, 2, 0, 1))}
PRIMES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31)


class Field:
    """F_q as the integers 0..q-1 (base-p digits = polynomial coefficients), with tables."""

    def __init__(self, q):
        if q in MODULI:
            p, mod = MODULI[q]
            k = len(mod) - 1
        elif q in PRIMES:
            p, mod, k = q, None, 1
        else:
            raise ValueError(f"unsupported field size {q}")
        self.q, self.p, self.k = q, p, k

        def digits(a):
            return [(a // p ** i) % p for i in range(k)]

        def number(ds):
            return sum(c * p ** i for i, c in enumerate(ds))

        self.add = [[number([(x + y) % p for x, y in zip(digits(a), digits(b))])
                     for b in range(q)] for a in range(q)]
        self.mul = []
        for a in range(q):
            row = []
            for b in range(q):
                if k == 1:
                    row.append(a * b % p)
                    continue
                prod = [0] * (2 * k - 1)
                for i, x in enumerate(digits(a)):
                    for j, y in enumerate(digits(b)):
                        prod[i + j] = (prod[i + j] + x * y) % p
                for deg in range(2 * k - 2, k - 1, -1):
                    c = prod[deg]
                    if c:
                        for i, coeff in enumerate(mod):
                            prod[deg - k + i] = (prod[deg - k + i] - c * coeff) % p
                row.append(number(prod[:k]))
            self.mul.append(row)
        self.neg = [next(b for b in range(q) if self.add[a][b] == 0) for a in range(q)]


# ---------------------------------------------------------------- the one-coordinate maps

def square_map(F, t, lam=1):
    """g_t(x) = lam * x^2 + t * x on F_q, as a list indexed by x."""
    return [F.add[F.mul[lam][F.mul[x][x]]][F.mul[t][x]] for x in range(F.q)]


def entropy(weights):
    """Shannon entropy in bits of a list of non-negative weights."""
    total = sum(weights)
    return -sum(w / total * math.log2(w / total) for w in weights if w > 0)


def pushforward(g, weights):
    out = [0] * len(weights)
    for x, w in enumerate(weights):
        out[g[x]] += w
    return out


def entropy_sum(F, weights, f=None):
    """sum over t in F_q of H(g_t # tau) in bits, g_t(x) = f(x) + t x (f = x^2 by default)."""
    total = 0.0
    for t in range(F.q):
        if f is None:
            g = square_map(F, t)
        else:
            g = [F.add[f[x]][F.mul[t][x]] for x in range(F.q)]
        total += entropy(pushforward(g, weights))
    return total


def entropy_sum_uniform(q):
    """The value of entropy_sum at the uniform tau: q log2 q - (q - 1)."""
    return q * math.log2(q) - (q - 1)


def exponent(q):
    """c_q = log2 q - (q - 1)/q, the exponent of the new bound (bits per coordinate)."""
    return math.log2(q) - (q - 1) / q


def new_base(q):
    return q * 2 ** (-(q - 1) / q)


def lower_base(q):
    """q^2 / (2q - 1): the base of the lower bounds of KLSS (Theorem 1) and Bukh-Chao."""
    return q * q / (2 * q - 1)


# Best previously published upper bounds on the base that we found (see README, section 2).
PREVIOUS = {
    2: (math.sqrt(2), "exact: Kakeya sets of F_2^n are difference bases (Banakh-Gavrylkiv)"),
    3: (3 / 2 ** (2 / 3), "KLSS Theorem 8, random linear maps (explicit: 2, KLSS Theorem 6)"),
    4: (4 / 2 ** 0.5, "KLSS Theorem 8, random linear maps (explicit: 3)"),
    5: (3.0, "KLSS Theorem 6, (q + 1)/2"),
    7: (4.0, "KLSS Theorem 6, (q + 1)/2"),
    8: ((5 * 8 + 2 * math.sqrt(8) + 5) / 8, "Kyureghyan-Muller-Wang Theorem 3.2"),
    9: (5.0, "KLSS Theorem 6, (q + 1)/2"),
    11: (6.0, "KLSS Theorem 6, (q + 1)/2"),
    13: (7.0, "KLSS Theorem 6, (q + 1)/2"),
    16: ((16 + 4) / 2, "Kyureghyan-Muller-Wang Theorem 2.2"),
}


# ---------------------------------------------------------------- blocks and weights

def composition(F, y):
    return [y.count(s) for s in range(F.q)]


def class_size(counts):
    """Number of vectors with these symbol counts (a multinomial coefficient)."""
    out, left = 1, sum(counts)
    for c in counts:
        out *= math.comb(left, c)
        left -= c
    return out


def split(x, m):
    return [tuple(x[i:i + m]) for i in range(0, len(x), m)]


def weight(F, x, m):
    """Product over the blocks of x of the size of the block's composition class."""
    w = 1
    for y in split(x, m):
        w *= class_size(composition(F, y))
    return w


def block_points(F, u, s=0, lam=1):
    """The q points of the block line with witness lam*u^2 + s*u: point t is lam*u^2 + (s+t)*u."""
    return [tuple(F.add[F.mul[lam][F.mul[x][x]]][F.mul[F.add[s][t]][x]] for x in u)
            for t in range(F.q)]


def block_weights(F, u):
    """Class sizes of g_t(u) = u^2 + t u for t in F_q (the block line with shift 0)."""
    return [class_size(composition(F, y)) for y in block_points(F, u)]


def line_through(F, d, m, shifts, lams=None):
    """The line {a + t d} with a = lam_j d_j^2 + s_j d_j on block j, listed by t."""
    blocks = split(d, m)
    lams = lams or [1] * len(blocks)
    per_block = [block_points(F, u, s, lam) for u, s, lam in zip(blocks, shifts, lams)]
    return [sum((pts[t] for pts in per_block), ()) for t in range(F.q)]


def min_max_weight(F, d, m):
    """min over shift tuples of the largest weight on the line; returns (weight, shifts)."""
    vs = [block_weights(F, u) for u in split(d, m)]
    best = None
    for shifts in product(range(F.q), repeat=len(vs)):
        worst = 0
        for t in range(F.q):
            w = 1
            for v, s in zip(vs, shifts):
                w *= v[F.add[s][t]]
            worst = max(worst, w)
        if best is None or worst < best[0]:
            best = (worst, shifts)
    return best


def hoeffding_log2(F, d, m):
    """The bound of Lemma 3 for this direction: mean log-cost plus m log2(q) sqrt(r ln q)."""
    vs = [block_weights(F, u) for u in split(d, m)]
    mean = sum(sum(math.log2(w) for w in v) / F.q for v in vs)
    return mean + m * math.log2(F.q) * math.sqrt(len(vs) * math.log(F.q))


def vectors(q, n):
    return list(product(range(q), repeat=n))


def theta_star(F, m, r):
    """Largest min_max_weight over nonzero directions of F_q^(rm)."""
    return max(min_max_weight(F, d, m)[0] for d in vectors(F.q, r * m) if any(d))


def kakeya_set(F, m, r, theta):
    return {x for x in vectors(F.q, r * m) if weight(F, x, m) <= theta}


def directions(F, n):
    for d in product(range(F.q), repeat=n):
        nonzero = [c for c in d if c]
        if nonzero and nonzero[0] == 1:
            yield d


def is_kakeya(F, n, K):
    """Brute force: every direction has a full line inside K."""
    K = set(K)
    for d in directions(F, n):
        multiples = [tuple(F.mul[t][c] for c in d) for t in range(F.q)]
        if not any(all(tuple(F.add[a][b] for a, b in zip(x, td)) in K for td in multiples)
                   for x in K):
            return False
    return True


def theorem_log2(q, m, r):
    """log2 of the Theorem's bound for F_q^(rm):
    r log2 C(m+q-1, q-1) + r m c_q + m log2(q) sqrt(r ln q)."""
    return (r * math.log2(math.comb(m + q - 1, q - 1)) + r * m * exponent(q)
            + m * math.log2(q) * math.sqrt(r * math.log(q)))


def theorem_base(q, m, r):
    return 2 ** (theorem_log2(q, m, r) / (r * m))


# ---------------------------------------------------------------- q = 3, deterministic

F3 = Field(3)


def central(m):
    return math.comb(m, m // 2)


def q3_peak(m):
    """Q(m) = max over a + b + c = m of C(m,a) C(m,b) C(m,c), attained at the balanced split."""
    parts = [m // 3 + (1 if i < m % 3 else 0) for i in range(3)]
    return math.prod(math.comb(m, a) for a in parts)


def q3_peak_brute(m):
    return max(math.comb(m, a) * math.comb(m, b) * math.comb(m, m - a - b)
               for a in range(m + 1) for b in range(m + 1 - a))


def in_k3(x, m):
    """Membership in K3(m, r): every block uses at most two symbols and
    (product of the blocks' class sizes)^3 <= Q(m)^r * C(m, m//2)^2."""
    r = len(x) // m
    w = 1
    for y in split(x, m):
        if len(set(y)) > 2:
            return False
        w *= class_size(composition(F3, y))
    return w ** 3 <= q3_peak(m) ** r * central(m) ** 2


def k3_witness(d, m):
    """A point a such that a, a + d, a + 2d all lie in K3, by the balancing rule of section 5:
    on each block, give the largest of C(m,z), C(m,p), C(m,k) to the point with the smallest
    load so far. The six orders come from lam in {1, 2} (that is, +-x^2) and the shift s."""
    loads = [1, 1, 1]
    a = []
    for u in split(d, m):
        z, p, k = (u.count(s) for s in range(3))
        cz, cp, ck = math.comb(m, z), math.comb(m, p), math.comb(m, k)
        options = []
        for lam, vals in ((1, (cz, cp, ck)), (2, (cz, ck, cp))):
            for s in range(3):
                options.append((lam, s, [vals[(t + s) % 3] for t in range(3)]))
        order = sorted(range(3), key=lambda t: loads[t])
        wanted = sorted((cz, cp, ck), reverse=True)
        target = [0, 0, 0]
        for t, v in zip(order, wanted):
            target[t] = v
        lam, s, vals = next(o for o in options if o[2] == target)
        loads = [loads[t] * vals[t] for t in range(3)]
        a.extend((lam * x * x + s * x) % 3 for x in u)
    return tuple(a)


def k3_log2_bound(m, r):
    """log2 of |K3(m, r)| <= (3m)^r * Q(m)^(r/3) * C(m, m//2)^(2/3)."""
    return (r * math.log2(3 * m) + r * math.log2(q3_peak(m)) / 3
            + 2 * math.log2(central(m)) / 3)


def k3_base(m, r):
    return 2 ** (k3_log2_bound(m, r) / (r * m))


# ---------------------------------------------------------------- command line

def print_table():
    print(" q  lower    previous  new      previous bound from")
    for q in sorted(PREVIOUS):
        prev, why = PREVIOUS[q]
        print(f"{q:2d}  {lower_base(q):.4f}  {prev:.4f}    {new_base(q):.4f}   {why}")


def print_small():
    for q, m, r in ((3, 2, 2), (3, 3, 2), (3, 2, 3), (4, 2, 2), (5, 2, 2)):
        F = Field(q)
        theta = theta_star(F, m, r)
        K = kakeya_set(F, m, r, theta)
        print(f"q={q} m={m} r={r}: theta*={theta} |K|={len(K)} of {q ** (r * m)} "
              f"kakeya={is_kakeya(F, r * m, K)}")
    for m, r in ((2, 2), (3, 2), (2, 3)):
        K = [x for x in vectors(3, m * r) if in_k3(x, m)]
        print(f"K3 m={m} r={r}: |K3|={len(K)} kakeya={is_kakeya(F3, m * r, K)}")
    for m, r in ((150, 25), (300, 100), (3000, 3000)):
        print(f"K3 m={m} r={r} n={m * r}: base <= {k3_base(m, r):.5f}")


if __name__ == "__main__":
    {"table": print_table, "small": print_small}[sys.argv[1] if len(sys.argv) > 1 else "table"]()
