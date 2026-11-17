"""Bezout-Jacobian bound for finite-field Kakeya blocks (note a170).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only. Self-contained (imports no other repo module).

For a map P of F_q^k (q an odd prime here), A_t(x) = P(x) + t x and
Lambda(P) = sum_t H(X | A_t(X)) in bits, X uniform on F_q^k.
For a quadratic map, DP(y) is computed exactly by central differences:
P(y + e) - P(y - e) = 2 DP(y) e.
"""
import itertools
import math
import random


def points(q, k):
    return list(itertools.product(range(q), repeat=k))


def add(u, v, q):
    return tuple((a + b) % q for a, b in zip(u, v))


def mat_vec(M, v, q):
    return tuple(sum(M[i][j] * v[j] for j in range(len(v))) % q for i in range(len(M)))


def rank_mod(rows, q):
    """Rank over F_q (q prime) of a matrix given as a list of rows."""
    m = [[a % q for a in r] for r in rows]
    nr = len(m)
    nc = len(m[0]) if nr else 0
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if m[i][c]:
                piv = i
                break
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][c], q - 2, q)
        m[r] = [(a * inv) % q for a in m[r]]
        for i in range(nr):
            if i != r and m[i][c]:
                f = m[i][c]
                m[i] = [(a - f * b) % q for a, b in zip(m[i], m[r])]
        r += 1
        if r == nr:
            break
    return r


def random_invertible(q, k, rng):
    while True:
        M = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
        if rank_mod(M, q) == k:
            return M


def table_of(fn, q, k):
    return {x: tuple(v % q for v in fn(x)) for x in points(q, k)}


def fibres(table, q, t):
    groups = {}
    for x, px in table.items():
        key = tuple((a + t * b) % q for a, b in zip(px, x))
        groups.setdefault(key, []).append(x)
    return list(groups.values())


def lam(table, q):
    n = len(table)
    total = 0.0
    for t in range(q):
        for f in fibres(table, q, t):
            m = len(f)
            total += m * math.log2(m) / n
    return total


def jacobian(table, y, q, k):
    """DP(y) as a list of rows, exact for maps of degree <= 2 (q odd)."""
    inv2 = (q + 1) // 2
    cols = []
    for j in range(k):
        yp = tuple((y[i] + (1 if i == j else 0)) % q for i in range(k))
        ym = tuple((y[i] - (1 if i == j else 0)) % q for i in range(k))
        a = table[yp]
        b = table[ym]
        cols.append([((a[i] - b[i]) * inv2) % q for i in range(k)])
    return [[cols[j][i] for j in range(k)] for i in range(k)]


def corank_shift(J, t, q):
    k = len(J)
    M = [[(J[i][j] + (t if i == j else 0)) % q for j in range(k)] for i in range(k)]
    return k - rank_mod(M, q)


def bezout_data(table, q, k):
    """Return (Lambda, sum_x g(DP(x)), list of fibre sums sum_{y in F} 2^{c_t(y)},
    stronger per-fibre bound value B2 = sum_t sum_F (|F|/n) (k - log2 avg_F 2^c))."""
    cor = {}
    for y in table:
        J = jacobian(table, y, q, k)
        cor[y] = [corank_shift(J, t, q) for t in range(q)]
    n = len(table)
    lam_ = 0.0
    b2 = 0.0
    sums = []
    for t in range(q):
        for f in fibres(table, q, t):
            m = len(f)
            s = sum(2 ** cor[y][t] for y in f)
            lam_ += m * math.log2(m) / n
            b2 += (m / n) * (k - math.log2(s / m))
            sums.append(s)
    gsum = sum(sum(c) for c in cor.values())
    return lam_, gsum, sums, b2


# ---------- families satisfying the hypothesis of Theorem 50 ----------

def frame_map(q, k, rng):
    """P_i(x) = a_i x_i^2 + l_i x_i + c_i with a_i != 0."""
    a = [rng.randrange(1, q) for _ in range(k)]
    l = [rng.randrange(q) for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]
    return lambda x: tuple(a[i] * x[i] * x[i] + l[i] * x[i] + c[i] for i in range(k))


def sq(z, q):
    return tuple(v * v % q for v in z)


def mixed_frame_map(q, k, rng):
    """P(x) = S sq(T x) + L x + c, S and T invertible, L arbitrary."""
    S = random_invertible(q, k, rng)
    T = random_invertible(q, k, rng)
    L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]

    def P(x):
        u = mat_vec(S, sq(mat_vec(T, x, q), q), q)
        w = mat_vec(L, x, q)
        return tuple((u[i] + w[i] + c[i]) % q for i in range(k))
    return P


def irreducible_modulus(q, k):
    """Monic s^k + c1 s + c0 (k = 2 or 3) with no root in F_q, hence irreducible."""
    for c0 in range(1, q):
        for c1 in range(q):
            m = [c0, c1] + [0] * (k - 2) + [1]
            if all(sum(m[j] * pow(s, j, q) for j in range(k + 1)) % q for s in range(q)):
                return m
    raise ValueError("no modulus found")


def polymulmod(a, b, m, q):
    k = len(m) - 1
    prod = [0] * (2 * k - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                prod[i + j] = (prod[i + j] + ai * bj) % q
    for d in range(2 * k - 2, k - 1, -1):
        c = prod[d]
        if c:
            prod[d] = 0
            for j in range(k):
                prod[d - k + j] = (prod[d - k + j] - c * m[j]) % q
    return tuple(prod[:k])


def field_square_map(q, k):
    m = irreducible_modulus(q, k)
    return lambda x: polymulmod(x, x, m, q)


def mixed_field_map(q, k, rng):
    """P(x) = S (T x)^2 + L x + c in F_q[s]/(m), S and T invertible."""
    m = irreducible_modulus(q, k)
    S = random_invertible(q, k, rng)
    T = random_invertible(q, k, rng)
    L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]

    def P(x):
        z = mat_vec(T, x, q)
        u = mat_vec(S, polymulmod(z, z, m, q), q)
        w = mat_vec(L, x, q)
        return tuple((u[i] + w[i] + c[i]) % q for i in range(k))
    return P


def swap_map(x):
    return (x[1] * x[1], x[0] * x[0])


def sylvester_nonzero(f, g, q):
    """f, g = (a, b, c) for binary forms a X^2 + b XY + c Y^2. True iff the
    resultant is nonzero mod q, i.e. no common zero in P^1 over the closure."""
    a1, b1, c1 = f
    a2, b2, c2 = g
    M = [[a1, b1, c1, 0], [0, a1, b1, c1], [a2, b2, c2, 0], [0, a2, b2, c2]]
    return rank_mod(M, q) == 4


def random_plane_quadratic(q, rng):
    """A random quadratic map of F_q^2 whose top forms have no common zero
    over the algebraic closure (checked by the Sylvester resultant)."""
    while True:
        f = tuple(rng.randrange(q) for _ in range(3))
        g = tuple(rng.randrange(q) for _ in range(3))
        if sylvester_nonzero(f, g, q):
            break
    lin = [[rng.randrange(q) for _ in range(3)] for _ in range(2)]
    forms = (f, g)

    def P(x):
        out = []
        for i in range(2):
            a, b, c = forms[i]
            l1, l2, e = lin[i]
            out.append(a * x[0] * x[0] + b * x[0] * x[1] + c * x[1] * x[1]
                       + l1 * x[0] + l2 * x[1] + e)
        return tuple(out)
    return P
