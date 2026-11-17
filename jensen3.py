# SPDX-License-Identifier: Apache-2.0
"""Exact checks for note a166: a Jensen bound for the Kakeya information loss, and
Conjecture C_q(3) for every map of F_q^3 of degree <= 2 (q odd).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Apache-2.0. Standard library only. Every q used here is a PRIME (arithmetic mod q).

Maps are Python callables x -> tuple, turned into a lookup table over F_q^k.
Lambda(P) = sum_t H(X | P(X) + tX) is handled exactly through the integer
W(P) = prod_t prod_{fibres S of P + tI} |S|^|S|, since q^k Lambda = log2 W.
"""

import itertools
import random
from collections import Counter

# ----------------------------------------------------------------------------
# basic arithmetic
# ----------------------------------------------------------------------------


def pts(q, k=3):
    return list(itertools.product(range(q), repeat=k))


def idx(x, q):
    i = 0
    for c in reversed(x):
        i = i * q + c
    return i


def vadd(x, y, q):
    return tuple((a + b) % q for a, b in zip(x, y))


def vsub(x, y, q):
    return tuple((a - b) % q for a, b in zip(x, y))


def vscale(s, x, q):
    return tuple((s * a) % q for a in x)


def dot(x, y, q):
    return sum(a * b for a, b in zip(x, y)) % q


def cross(u, v, q):
    return ((u[1] * v[2] - u[2] * v[1]) % q,
            (u[2] * v[0] - u[0] * v[2]) % q,
            (u[0] * v[1] - u[1] * v[0]) % q)


def det3(a, b, c, q):
    """Determinant of the 3x3 matrix with columns a, b, c."""
    return dot(a, cross(b, c, q), q)


def parallel(u, v, q):
    """True iff v lies in F_q u (u nonzero, k = 3); v = 0 counts as parallel."""
    return cross(u, v, q) == (0, 0, 0)


def matvec(M, x, q):
    return tuple(sum(M[i][j] * x[j] for j in range(len(x))) % q for i in range(len(M)))


def unit(i, k=3):
    return tuple(1 if j == i else 0 for j in range(k))


def rank(vectors, q):
    rows = [list(v) for v in vectors]
    if not rows:
        return 0
    ncol = len(rows[0])
    r = 0
    for col in range(ncol):
        piv = None
        for i in range(r, len(rows)):
            if rows[i][col] % q:
                piv = i
                break
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][col], q - 2, q)
        rows[r] = [(a * inv) % q for a in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] % q:
                f = rows[i][col]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def nullspace(rows, n, q):
    """Basis of {v in F_q^n : row . v = 0 for every row} (rows of length n)."""
    m = [list(r) for r in rows if any(c % q for c in r)]
    pivots = []
    r = 0
    for col in range(n):
        piv = None
        for i in range(r, len(m)):
            if m[i][col] % q:
                piv = i
                break
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        inv = pow(m[r][col], q - 2, q)
        m[r] = [(a * inv) % q for a in m[r]]
        for i in range(len(m)):
            if i != r and m[i][col] % q:
                f = m[i][col]
                m[i] = [(a - f * b) % q for a, b in zip(m[i], m[r])]
        pivots.append(col)
        r += 1
        if r == len(m):
            break
    free = [c for c in range(n) if c not in pivots]
    basis = []
    for f in free:
        v = [0] * n
        v[f] = 1
        for row_i, pc in enumerate(pivots):
            v[pc] = (-m[row_i][f]) % q
        basis.append(v)
    return basis


def directions(q, k=3):
    """Projective points: first nonzero coordinate equal to 1."""
    out = []
    for x in pts(q, k):
        nz = [c for c in x if c]
        if nz and nz[0] == 1:
            out.append(x)
    return out


# ----------------------------------------------------------------------------
# maps and Lambda
# ----------------------------------------------------------------------------


def table_of(f, q, k=3):
    tab = [None] * (q ** k)
    for x in pts(q, k):
        tab[idx(x, q)] = tuple(c % q for c in f(x))
    return tab


def fibre_sizes(tab, q, k=3):
    allp = pts(q, k)
    out = []
    for t in range(q):
        cnt = Counter()
        for x in allp:
            y = tab[idx(x, q)]
            cnt[tuple((y[i] + t * x[i]) % q for i in range(k))] += 1
        out.append(sorted(cnt.values()))
    return out


def weight(sizes):
    """W = prod n^n over all fibres of all t; q^k Lambda = log2 W."""
    W = 1
    for lst in sizes:
        for n in lst:
            W *= n ** n
    return W


def pair_total(sizes):
    """Number of ordered pairs x != y with P(x)-P(y) parallel to x-y (= sum_w Pi_w)."""
    return sum(n * (n - 1) for lst in sizes for n in lst)


def jensen_holds(sizes, q, k=3):
    """Theorem 42: q^k Lambda <= q^(k+1) log2(1 + S/q^(k+1)), S = sum_w Pi_w.
    Exact form: W * N^N <= (N + S)^N with N = q^(k+1)."""
    N = q ** (k + 1)
    S = pair_total(sizes)
    return weight(sizes) * N ** N <= (N + S) ** N


def conjecture_holds(sizes, q, k=3):
    """C_q(k): Lambda <= k(q-1), i.e. W <= 2^(k(q-1) q^k)."""
    return weight(sizes) <= 1 << (k * (q - 1) * q ** k)


def jensen_strict_below(sizes, q, k=3):
    """The Jensen bound itself is < k(q-1): ((N+S)/N)^q < 2^(k(q-1)), N = q^(k+1)."""
    N = q ** (k + 1)
    S = pair_total(sizes)
    return (N + S) ** q < (1 << (k * (q - 1))) * N ** q


# ----------------------------------------------------------------------------
# degree-2 structure read off the table (k = 3, q odd prime)
# ----------------------------------------------------------------------------


def P_at(tab, x, q):
    return tab[idx(x, q)]


def beta(tab, x, w, q):
    """Polar form of the quadratic part: P(x+w) - P(x) - P(w) + P(0)."""
    z = (0, 0, 0)
    a = P_at(tab, vadd(x, w, q), q)
    b = P_at(tab, x, q)
    c = P_at(tab, w, q)
    d = P_at(tab, z, q)
    return tuple((a[i] - b[i] - c[i] + d[i]) % q for i in range(3))


def lin(tab, w, q):
    """L w = P(w) - P(0) - Q(w), Q(w) = beta(w, w)/2."""
    inv2 = (q + 1) // 2
    bw = beta(tab, w, w, q)
    pw = P_at(tab, w, q)
    p0 = P_at(tab, (0, 0, 0), q)
    return tuple((pw[i] - p0[i] - inv2 * bw[i]) % q for i in range(3))


def quadratic_part_zero(tab, q):
    for i in range(3):
        for j in range(3):
            if beta(tab, unit(i), unit(j), q) != (0, 0, 0):
                return False
    return True


def pencil_columns(tab, w, q):
    return [beta(tab, unit(0), w, q), beta(tab, unit(1), w, q),
            beta(tab, unit(2), w, q), tuple(w), lin(tab, w, q)]


def minors_vanish(tab, w, q):
    cols = pencil_columns(tab, w, q)
    for a, b, c in itertools.combinations(range(5), 3):
        if det3(cols[a], cols[b], cols[c], q):
            return False
    return True


def z_is_whole_plane(tab, q):
    """All ten 3x3 minors vanish identically. For q >= 5 the minors are cubic forms with
    every variable of degree <= 3 < q, so vanishing on F_q^3 is vanishing identically."""
    assert q >= 5
    for w in pts(q):
        if any(w) and not minors_vanish(tab, w, q):
            return False
    return True


def rational_Z(tab, q):
    return [w for w in directions(q) if minors_vanish(tab, w, q)]


def r_and_active(tab, w, q):
    bs = [beta(tab, unit(j), w, q) for j in range(3)]
    r_bw = rank(bs + [tuple(w)], q)
    r = r_bw - 1
    act = rank(bs + [tuple(w), lin(tab, w, q)], q) == r_bw
    return r, act


def pi_w(tab, w, q):
    c = 0
    for x in pts(q):
        px = P_at(tab, x, q)
        for lam in range(1, q):
            y = vadd(x, vscale(lam, w, q), q)
            if parallel(w, vsub(P_at(tab, y, q), px, q), q):
                c += 1
    return c


def classify(tab, q):
    """Per direction: (r_w, active, brute-force Pi_w)."""
    return {w: r_and_active(tab, w, q) + (pi_w(tab, w, q),) for w in directions(q)}


def respects_subspace(tab, q):
    """Does P respect a nonzero proper subspace V (P(x+v)-P(x) in V for all x, v in V)?
    q prime, so it suffices to test v in a basis of V (telescoping)."""
    allp = pts(q)
    for u in directions(q):  # lines F_q u
        if all(parallel(u, vsub(P_at(tab, vadd(x, u, q), q), P_at(tab, x, q), q), q)
               for x in allp):
            return True
    for phi in directions(q):  # planes ker phi
        ker = [v for v in allp if any(v) and dot(phi, v, q) == 0]
        v1 = ker[0]
        v2 = next(v for v in ker if not parallel(v1, v, q))
        if all(dot(phi, vsub(P_at(tab, vadd(x, v, q), q), P_at(tab, x, q), q), q) == 0
               for x in allp for v in (v1, v2)):
            return True
    return False


# ----------------------------------------------------------------------------
# families of maps
# ----------------------------------------------------------------------------


def random_quadratic(q, rng, k=3):
    monos = [(i, j) for i in range(k) for j in range(i, k)]
    Qc = [{m: rng.randrange(q) for m in monos} for _ in range(k)]
    L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]

    def f(x):
        out = []
        for comp in range(k):
            s = c[comp]
            for (i, j), a in Qc[comp].items():
                s += a * x[i] * x[j]
            for j in range(k):
                s += L[comp][j] * x[j]
            out.append(s % q)
        return tuple(out)
    return f


def random_map(q, rng, k):
    """An arbitrary map F_q^k -> F_q^k (any degree)."""
    vals = {x: tuple(rng.randrange(q) for _ in range(k)) for x in pts(q, k)}
    return lambda x: vals[tuple(x)]


def family(q, rho, delta):
    """F_{rho,delta} of a165, Theorem 41; E = F_{-1/2, 0}."""
    def f(x):
        x1, x2, x3 = x
        s = x1 + x2
        return (((2 * x1 + x2) * x3 - rho * s * s - 2 * x1 * x1 - 3 * x1 * x2
                 - x2 * x2 - delta * s) % q,
                (x1 * s) % q,
                (x1 * x3) % q)
    return f


def E_map(q):
    return family(q, (q - 1) // 2, 0)  # rho = -1/2 mod q


def type_b(q, rng):
    """P(x) = m(x)x + m(x)^2 a + m(x) v + s x + h(x) c with m(c) != 0 (a165, Section 1)."""
    while True:
        m = tuple(rng.randrange(q) for _ in range(3))
        c = tuple(rng.randrange(q) for _ in range(3))
        if dot(m, c, q):
            break
    a = tuple(rng.randrange(q) for _ in range(3))
    v = tuple(rng.randrange(q) for _ in range(3))
    s = rng.randrange(q)
    h = random_quadratic(q, rng, 3)

    def f(x):
        mx = dot(m, x, q)
        hx = h(x)[0]
        return tuple((mx * x[i] + mx * mx * a[i] + mx * v[i] + s * x[i] + hx * c[i]) % q
                     for i in range(3))
    return f


def line_respecting(q, rng):
    """P(x) = s x + h(x) u + const: the shape forced by Proposition 50 (non-regular case)."""
    u = tuple(rng.randrange(q) for _ in range(3))
    while not any(u):
        u = tuple(rng.randrange(q) for _ in range(3))
    s = rng.randrange(q)
    h = random_quadratic(q, rng, 3)
    c0 = tuple(rng.randrange(q) for _ in range(3))

    def f(x):
        hx = h(x)[0]
        return tuple((s * x[i] + hx * u[i] + c0[i]) % q for i in range(3))
    return f


# ----------------------------------------------------------------------------
# Lemma 118 / Lemma 119 / Proposition 50 as linear algebra over F_q (q >= 5)
# ----------------------------------------------------------------------------


def is_regular(T, q):
    """Minimal polynomial of degree 3: I, T, T^2 linearly independent."""
    I = [[1 if i == j else 0 for j in range(3)] for i in range(3)]
    T2 = [[sum(T[i][l] * T[l][j] for l in range(3)) % q for j in range(3)] for i in range(3)]
    flat = [[M[i][j] % q for i in range(3) for j in range(3)] for M in (I, T, T2)]
    return rank(flat, q) == 3


def span_lemma_rows(T, q):
    """Rows of the linear system det(w, Tw, Aw) = 0 for all w in F_q^3, unknowns A_ij
    (index 3i+j). Valid as a polynomial identity test for q >= 5."""
    rows = []
    for w in pts(q):
        if not any(w):
            continue
        Tw = matvec(T, w, q)
        d = [det3(w, Tw, unit(i), q) for i in range(3)]
        rows.append([(d[i] * w[j]) % q for i in range(3) for j in range(3)])
    return rows


def symmetric_rows(T, q):
    """a(y) w + b(y) T w = a(w) y + b(w) T y for y, w in the standard basis.
    Unknowns a_0..a_2 (0..2), b_0..b_2 (3..5)."""
    rows = []
    for i in range(3):
        for j in range(3):
            for l in range(3):
                row = [0] * 6
                # a(e_i) (e_j)_l + b(e_i) (T e_j)_l - a(e_j) (e_i)_l - b(e_j) (T e_i)_l
                row[i] += 1 if j == l else 0
                row[3 + i] += T[l][j]
                row[j] -= 1 if i == l else 0
                row[3 + j] -= T[l][i]
                rows.append([c % q for c in row])
    return rows


SYM_PAIRS = [(i, j) for i in range(3) for j in range(i, 3)]


def beta_var(i, j, l):
    """Index of unknown beta(e_i, e_j)_l (symmetric), 0..17."""
    a, b = min(i, j), max(i, j)
    return 3 * SYM_PAIRS.index((a, b)) + l


def pencil_system_rows(T, q):
    """Unknowns: symmetric beta (18) and L (9, index 18 + 3l + m). Conditions:
    det(w, Tw, beta(e_j, w)) = 0 for j = 0,1,2 and det(w, Tw, Lw) = 0, all w."""
    rows = []
    for w in pts(q):
        if not any(w):
            continue
        Tw = matvec(T, w, q)
        d = [det3(w, Tw, unit(l), q) for l in range(3)]
        for j in range(3):
            row = [0] * 27
            for m in range(3):
                for l in range(3):
                    row[beta_var(j, m, l)] = (row[beta_var(j, m, l)] + w[m] * d[l]) % q
            rows.append(row)
        row = [0] * 27
        for l in range(3):
            for m in range(3):
                row[18 + 3 * l + m] = (w[m] * d[l]) % q
        rows.append(row)
    return rows


def solution_beta(v):
    return {(i, j): tuple(v[beta_var(i, j, l)] for l in range(3)) for (i, j) in SYM_PAIRS}


def solution_L(v):
    return [[v[18 + 3 * l + m] for m in range(3)] for l in range(3)]


# ----------------------------------------------------------------------------
# numbers used in Theorem 43 / Corollary 132
# ----------------------------------------------------------------------------


def pibar_formula_times_q2(q, nD, nZ0):
    """q^2 * Pibar = (q-1)[q^2+q+1 + (q-1)|D| - |Z0|] for maps without full directions."""
    return (q - 1) * (q * q + q + 1 + (q - 1) * nD - nZ0)
