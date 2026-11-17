"""splitgroup.py -- affine partner groups, orthogonal groups and pair counts of quadratic
maps of F_q^k, for note a171 of kakeya-small-fields.

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.
Standard library only, self-contained. All q are odd primes.

Conventions. A map P of F_q^k is stored as a table: table[i] = P(x) for the i-th vector x of
vectors(q, k) (itertools.product order, first coordinate most significant). A_t(x) = P(x) + t x.
An affine partner map is a triple (M, w, v) with A_t(Mx + t w + v) = A_t(x) for every x in
F_q^k and t in F_q. Since this difference is a polynomial of degree <= 2 < q in each variable,
checking all points of F_q^(k+1) is the same as checking the polynomial identity.
"""
import itertools
import math


# ----------------------------------------------------------------------------- vectors

def vectors(q, k):
    return list(itertools.product(range(q), repeat=k))


def index_of(v, q):
    i = 0
    for a in v:
        i = i * q + a
    return i


# ----------------------------------------------------------------------------- matrices

def identity(k):
    return tuple(tuple(1 if i == j else 0 for j in range(k)) for i in range(k))


def mat_vec(M, x, q):
    k = len(x)
    return tuple(sum(M[i][j] * x[j] for j in range(k)) % q for i in range(len(M)))


def mat_mul(A, B, q):
    r = len(B)
    m = len(B[0])
    return tuple(tuple(sum(A[i][l] * B[l][j] for l in range(r)) % q for j in range(m))
                 for i in range(len(A)))


def mat_inv(M, q):
    """Inverse of M over F_q (q prime), or None if M is singular."""
    k = len(M)
    A = [[M[i][j] % q for j in range(k)] + [1 if i == j else 0 for j in range(k)]
         for i in range(k)]
    for col in range(k):
        piv = None
        for r in range(col, k):
            if A[r][col] % q:
                piv = r
                break
        if piv is None:
            return None
        A[col], A[piv] = A[piv], A[col]
        inv = pow(A[col][col], q - 2, q)
        A[col] = [(a * inv) % q for a in A[col]]
        for r in range(k):
            if r != col and A[r][col] % q:
                f = A[r][col]
                A[r] = [(a - f * b) % q for a, b in zip(A[r], A[col])]
    return tuple(tuple(row[k:]) for row in A)


def all_matrices(q, k):
    out = []
    for e in itertools.product(range(q), repeat=k * k):
        out.append(tuple(tuple(e[i * k:(i + 1) * k]) for i in range(k)))
    return out


def general_linear(q, k):
    """All (E, E^-1) with E in GL_k(F_q)."""
    out = []
    for M in all_matrices(q, k):
        Mi = mat_inv(M, q)
        if Mi is not None:
            out.append((M, Mi))
    return out


def random_gl(q, k, rng):
    while True:
        E = tuple(tuple(rng.randrange(q) for _ in range(k)) for _ in range(k))
        Ei = mat_inv(E, q)
        if Ei is not None:
            return E, Ei


# ----------------------------------------------------------------------------- quadratic maps

def eval_quad(P, x, q):
    """P = (Qc, L, c): P_i(x) = sum_{a<=b} Qc[i][a][b] x_a x_b + sum_a L[i][a] x_a + c[i]."""
    Qc, L, c = P
    k = len(x)
    out = []
    for i in range(k):
        s = c[i]
        Qi = Qc[i]
        Li = L[i]
        for a in range(k):
            xa = x[a]
            if xa:
                s += Li[a] * xa
                row = Qi[a]
                for b in range(a, k):
                    s += row[b] * xa * x[b]
        out.append(s % q)
    return tuple(out)


def table_of(P, q, k):
    return [eval_quad(P, x, q) for x in vectors(q, k)]


def random_quadratic(q, k, rng):
    Qc = [[[rng.randrange(q) if b >= a else 0 for b in range(k)] for a in range(k)]
          for _ in range(k)]
    L = [[rng.randrange(q) for _ in range(k)] for _ in range(k)]
    c = [rng.randrange(q) for _ in range(k)]
    return (Qc, L, c)


def frame_quadratic(q, k, rng):
    """(a_i x_i^2 + l_i x_i + c_i)_i with every a_i != 0."""
    Qc = [[[0] * k for _ in range(k)] for _ in range(k)]
    for i in range(k):
        Qc[i][i][i] = rng.randrange(1, q)
    L = [[rng.randrange(q) if i == j else 0 for j in range(k)] for i in range(k)]
    c = [rng.randrange(q) for _ in range(k)]
    return (Qc, L, c)


def conjugate_table(table, E, Einv, q, k):
    """Table of x -> E^-1 P(E x)."""
    return [mat_vec(Einv, table[index_of(mat_vec(E, x, q), q)], q) for x in vectors(q, k)]


def binary_resultant(Qc, q):
    """Resultant of the two binary quadratic top forms of a map of F_q^2.
    Nonzero exactly when they have no common zero in P^1 over the algebraic closure."""
    a1, b1, c1 = Qc[0][0][0], Qc[0][0][1], Qc[0][1][1]
    a2, b2, c2 = Qc[1][0][0], Qc[1][0][1], Qc[1][1][1]
    return ((a1 * c2 - a2 * c1) ** 2 - (a1 * b2 - a2 * b1) * (b1 * c2 - b2 * c1)) % q


def top_form_table(table, q, k):
    """Q(x) = (P(x) + P(-x))/2 - P(0) for a quadratic map P (q odd)."""
    half = (q + 1) // 2
    P0 = table[0]
    out = []
    for x in vectors(q, k):
        mx = tuple((-a) % q for a in x)
        px = table[index_of(x, q)]
        pm = table[index_of(mx, q)]
        out.append(tuple(((px[i] + pm[i]) * half - P0[i]) % q for i in range(k)))
    return out


def irreducible_modulus(q, k):
    """Monic polynomial of degree k in {2, 3} with no root in F_q (hence irreducible)."""
    for tail in itertools.product(range(q), repeat=k):
        m = list(tail) + [1]
        if all(sum(m[j] * pow(s, j, q) for j in range(k + 1)) % q for s in range(q)):
            return m
    raise ValueError("no modulus")


def field_square_table(q, k, L=None):
    """x -> x^2 + Lx on F_(q^k) = F_q[s]/(m), in the coordinates of the basis 1, s, ..."""
    m = irreducible_modulus(q, k)

    def square(a):
        prod = [0] * (2 * k - 1)
        for i in range(k):
            for j in range(k):
                prod[i + j] += a[i] * a[j]
        for d in range(2 * k - 2, k - 1, -1):
            c = prod[d] % q
            if c:
                for j in range(k + 1):
                    prod[d - k + j] -= c * m[j]
        return tuple(p % q for p in prod[:k])

    out = []
    for x in vectors(q, k):
        y = square(x)
        if L is not None:
            lx = mat_vec(L, x, q)
            y = tuple((y[i] + lx[i]) % q for i in range(k))
        out.append(y)
    return out


# ----------------------------------------------------------------------------- Lambda and pairs

def lam_pairs(table, q, k):
    """Return (Lambda, M, J) where Lambda = sum_t H(X | A_t X) in bits,
    M = #{(x, y, t): x != y, A_t(x) = A_t(y)} and J = sum_t log2(N_t / q^k)."""
    vecs = vectors(q, k)
    n = len(vecs)
    lam = 0.0
    jt = 0.0
    nsum = 0
    for t in range(q):
        counts = {}
        for idx, x in enumerate(vecs):
            p = table[idx]
            key = tuple((p[i] + t * x[i]) % q for i in range(k))
            counts[key] = counts.get(key, 0) + 1
        lam += sum(c * math.log2(c) for c in counts.values()) / n
        nt = sum(c * c for c in counts.values())
        nsum += nt
        jt += math.log2(nt / n)
    return lam, nsum - q * n, jt


# ----------------------------------------------------------------------------- groups

def shifted_tables(table, q, k):
    vecs = vectors(q, k)
    return [[tuple((table[j][i] + t * vecs[j][i]) % q for i in range(k))
             for j in range(len(vecs))] for t in range(q)]


def affine_partners(table, q, k, mats=None):
    """Every nontrivial affine partner map (M, w, v), by brute force over ALL k x k matrices M
    (singular ones included) and all (w, v) that pass the identity at x = 0."""
    vecs = vectors(q, k)
    A = shifted_tables(table, q, k)
    pairs = []
    for w in vecs:
        for v in vecs:
            ok = True
            for t in range(q):
                y = tuple((t * w[i] + v[i]) % q for i in range(k))
                if A[t][index_of(y, q)] != A[t][0]:
                    ok = False
                    break
            if ok:
                pairs.append((w, v))
    if mats is None:
        mats = all_matrices(q, k)
    I = identity(k)
    zero = (0,) * k
    pts = [(t, x, ix) for ix, x in reversed(list(enumerate(vecs))) for t in range(q)]
    found = []
    rk = range(k)
    for (w, v) in pairs:
        for M in mats:
            if M == I and w == zero and v == zero:
                continue
            good = True
            for (t, x, ix) in pts:
                y = tuple((sum(M[i][j] * x[j] for j in rk) + t * w[i] + v[i]) % q for i in rk)
                if A[t][index_of(y, q)] != A[t][ix]:
                    good = False
                    break
            if good:
                found.append((M, w, v))
    return found


def compose(g, h, q):
    """(g o h)(x, t) = g(h(x, t), t)."""
    Mg, wg, vg = g
    Mh, wh, vh = h
    k = len(wg)
    M = mat_mul(Mg, Mh, q)
    w = tuple((a + b) % q for a, b in zip(mat_vec(Mg, wh, q), wg))
    v = tuple((a + b) % q for a, b in zip(mat_vec(Mg, vh, q), vg))
    return (M, w, v)


def orthogonal_group(table, q, k, mats=None):
    """All k x k matrices M (singular ones included) with Q(Mx) = Q(x) for every x."""
    Qt = top_form_table(table, q, k)
    vecs = vectors(q, k)
    if mats is None:
        mats = all_matrices(q, k)
    out = []
    order = list(reversed(list(enumerate(vecs))))
    for M in mats:
        ok = True
        for ix, x in order:
            if Qt[index_of(mat_vec(M, x, q), q)] != Qt[ix]:
                ok = False
                break
        if ok:
            out.append(M)
    return out


def is_frame_conjugate(table, q, k, gl=None):
    """True iff some E in GL_k(F_q) makes every component i of E^-1 P(E x) depend on x_i only."""
    vecs = vectors(q, k)
    if gl is None:
        gl = general_linear(q, k)
    for E, Einv in gl:
        cache = {}
        ok = True
        for x in vecs:
            if x not in cache:
                cache[x] = mat_vec(Einv, table[index_of(mat_vec(E, x, q), q)], q)
            vx = cache[x]
            for i in range(k):
                proj = tuple(x[j] if j == i else 0 for j in range(k))
                if proj not in cache:
                    cache[proj] = mat_vec(Einv, table[index_of(mat_vec(E, proj, q), q)], q)
                if vx[i] != cache[proj][i]:
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


# ----------------------------------------------------------------------------- thresholds

CM_A_EXP = 13.0 / 3.0


def lw_error(k, q):
    """e_k(q) = (D-1)(D-2) q^(-1/2) + (5 D^(13/3) + D^2) q^(-1), D = 2^k - 1 (Remark 51.1)."""
    D = 2 ** k - 1
    return (D - 1) * (D - 2) / math.sqrt(q) + (5 * D ** CM_A_EXP + D * D) / q


def cm_threshold(k):
    """Cafure-Matera hypothesis q > 2(r+1) delta^2 with r = k+1, delta <= D."""
    D = 2 ** k - 1
    return 2 * (k + 2) * D * D


def case_a_ok(k, q):
    """q log2(D + e_k(q)) <= k(q-1), written as D + e_k(q) <= 2^(k(q-1)/q)."""
    D = 2 ** k - 1
    return q > cm_threshold(k) and D + lw_error(k, q) <= 2.0 ** (k * (q - 1) / q)


def q0_case_a(k):
    """Least integer q with case_a_ok(k, q); the condition is monotone in q."""
    lo = cm_threshold(k) + 1
    if case_a_ok(k, lo):
        return lo
    hi = lo
    while not case_a_ok(k, hi):
        hi *= 2
    while hi - lo > 1:
        mid = (lo + hi) // 2
        if case_a_ok(k, mid):
            hi = mid
        else:
            lo = mid
    return hi
