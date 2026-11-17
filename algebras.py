"""Quadratic Kakeya blocks as commutative algebras (note a172). Standard library only.

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0.

A commutative algebra A of dimension k over F_q (q an odd prime here) is given by structure
constants C[i][j] = e_i o e_j (a k-tuple), symmetric in i, j. Its squaring map x -> x o x is a
quadratic map of F_q^k, and every quadratic map with zero constant and zero linear part arises
this way (x o y = (Q(x+y) - Q(x) - Q(y)) / 2). For a map P let A_t(x) = P(x) + t x and

    Lambda(P) = sum_t H(X | A_t(X)),     X uniform on F_q^k (bits).
"""
import itertools
import math
import random
from collections import Counter


# ---------------------------------------------------------------- algebras

def mult(C, x, y, q):
    k = len(x)
    out = [0] * k
    for i in range(k):
        xi = x[i]
        if xi == 0:
            continue
        for j in range(k):
            c = xi * y[j] % q
            if c == 0:
                continue
            row = C[i][j]
            for l in range(k):
                if row[l]:
                    out[l] = (out[l] + c * row[l]) % q
    return tuple(out)


def square(C, x, q):
    return mult(C, x, x, q)


def mat_vec(L, x, q):
    return tuple(sum(L[i][j] * x[j] for j in range(len(x))) % q for i in range(len(L)))


def mult_matrix(C, a, q):
    """Matrix of R_a : x -> a o x."""
    k = len(a)
    cols = [mult(C, a, unit_vec(k, j), q) for j in range(k)]
    return [[cols[j][i] for j in range(k)] for i in range(k)]


def unit_vec(k, j):
    return tuple(1 if i == j else 0 for i in range(k))


def make_map(C, q, L=None, c=None):
    """P(x) = x o x + L x + c."""
    k = len(C)
    if L is None:
        L = [[0] * k for _ in range(k)]
    if c is None:
        c = (0,) * k

    def P(x):
        s = square(C, x, q)
        lx = mat_vec(L, x, q)
        return tuple((s[i] + lx[i] + c[i]) % q for i in range(k))
    return P


def all_vectors(q, k):
    return list(itertools.product(range(q), repeat=k))


def fibre_sizes(F, q, k):
    """Sorted list of the fibre size of each point x under F."""
    pts = all_vectors(q, k)
    img = [F(x) for x in pts]
    cnt = Counter(img)
    return sorted(cnt[v] for v in img)


def cond_entropy(F, q, k):
    """H(X | F(X)) for X uniform on F_q^k."""
    pts = all_vectors(q, k)
    cnt = Counter(F(x) for x in pts)
    n = q ** k
    return sum(m * math.log2(m) for m in cnt.values()) / n


def shifted(P, q, t):
    def A(x):
        y = P(x)
        return tuple((y[i] + t * x[i]) % q for i in range(len(x)))
    return A


def kakeya_lambda(P, q, k):
    return sum(cond_entropy(shifted(P, q, t), q, k) for t in range(q))


def lambda_terms(P, q, k):
    return [cond_entropy(shifted(P, q, t), q, k) for t in range(q)]


def find_unit(C, q):
    k = len(C)
    basis = [unit_vec(k, j) for j in range(k)]
    for e in all_vectors(q, k):
        if all(mult(C, e, b, q) == b for b in basis):
            return e
    return None


def is_associative(C, q):
    k = len(C)
    B = [unit_vec(k, j) for j in range(k)]
    for a in B:
        for b in B:
            ab = mult(C, a, b, q)
            for c in B:
                if mult(C, ab, c, q) != mult(C, a, mult(C, b, c, q), q):
                    return False
    return True


# ---------------------------------------------------------------- constructions

def poly_mulmod(a, b, f, q):
    """a*b mod f; polys low -> high; f monic of degree k."""
    k = len(f) - 1
    prod = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            prod[i + j] = (prod[i + j] + ai * bj) % q
    for d in range(len(prod) - 1, k - 1, -1):
        c = prod[d]
        if c:
            for i in range(k + 1):
                prod[d - k + i] = (prod[d - k + i] - c * f[i]) % q
    out = prod[:k] + [0] * max(0, k - len(prod))
    return tuple(out[:k])


def poly_algebra(f, q):
    """F_q[s]/(f), f monic (coefficients low -> high), basis 1, s, ..., s^(k-1)."""
    k = len(f) - 1
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            a = [0] * i + [1]
            b = [0] * j + [1]
            C[i][j] = poly_mulmod(a, b, f, q)
    return C


def monic_polys(q, k):
    for low in itertools.product(range(q), repeat=k):
        yield list(low) + [1]


def poly_roots(f, q):
    return [r for r in range(q) if sum(c * pow(r, i, q) for i, c in enumerate(f)) % q == 0]


def is_irreducible(f, q):
    """Brute force: no monic factor of degree 1..k//2."""
    k = len(f) - 1
    for d in range(1, k // 2 + 1):
        for g in monic_polys(q, d):
            if poly_rem(f, g, q) == [0] * d:
                return False
    return True


def poly_rem(f, g, q):
    r = list(f)
    dg = len(g) - 1
    for d in range(len(r) - 1, dg - 1, -1):
        c = r[d]
        if c:
            for i in range(dg + 1):
                r[d - dg + i] = (r[d - dg + i] - c * g[i]) % q
    return r[:dg]


def truncated(q, k):
    """F_q[s]/(s^k)."""
    return poly_algebra([0] * k + [1], q)


def square_zero_local(q, m):
    """F_q[s_1..s_m]/(s_i s_j): basis 1, s_1, ..., s_m (dimension m + 1)."""
    k = m + 1
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i == 0:
                C[i][j] = unit_vec(k, j)
            elif j == 0:
                C[i][j] = unit_vec(k, i)
            else:
                C[i][j] = (0,) * k
    return C


def nil_truncated(q, k):
    """The maximal ideal (s) of F_q[s]/(s^(k+1)): basis s, ..., s^k; non-unital, nilpotent."""
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            d = (i + 1) + (j + 1)
            C[i][j] = unit_vec(k, d - 1) if d <= k else (0,) * k
    return C


def product(C1, C2):
    k1, k2 = len(C1), len(C2)
    k = k1 + k2
    C = [[(0,) * k for _ in range(k)] for _ in range(k)]
    for i in range(k1):
        for j in range(k1):
            C[i][j] = tuple(C1[i][j]) + (0,) * k2
    for i in range(k2):
        for j in range(k2):
            C[k1 + i][k1 + j] = (0,) * k1 + tuple(C2[i][j])
    return C


def unitization(C):
    """A^+ = F_q 1 + A, basis 1, e_1, ..., e_k."""
    k = len(C)
    K = k + 1
    D = [[None] * K for _ in range(K)]
    for i in range(K):
        for j in range(K):
            if i == 0:
                D[i][j] = unit_vec(K, j)
            elif j == 0:
                D[i][j] = unit_vec(K, i)
            else:
                D[i][j] = (0,) + tuple(C[i - 1][j - 1])
    return D


def extend_linear(L):
    """L'(tau 1 + a) = (0, L a)."""
    k = len(L)
    M = [[0] * (k + 1)]
    for i in range(k):
        M.append([0] + list(L[i]))
    return M


def random_commutative(q, k, rng):
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(i, k):
            v = tuple(rng.randrange(q) for _ in range(k))
            C[i][j] = v
            C[j][i] = v
    return C


def random_unital(q, k, rng):
    """Random commutative algebra with e_0 as unit (not associative in general)."""
    C = random_commutative(q, k, rng)
    for j in range(k):
        C[0][j] = unit_vec(k, j)
        C[j][0] = unit_vec(k, j)
    return C


def random_matrix(q, k, rng):
    return [[rng.randrange(q) for _ in range(k)] for _ in range(k)]


def frame_algebra(q, a):
    """Coordinatewise product scaled: e_i o e_i = a_i e_i (a_i != 0)."""
    k = len(a)
    C = [[(0,) * k for _ in range(k)] for _ in range(k)]
    for i in range(k):
        C[i][i] = tuple(a[i] if l == i else 0 for l in range(k))
    return C


def g_map_algebra(q, phi):
    """a167's G_n: (u, s) o (w, t) = (s w + t u, phi(u, w)); phi a symmetric n x n matrix.
    Basis e_1..e_n (the u part), then e_(n+1) (the s part)."""
    n = len(phi)
    k = n + 1
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            out = [0] * k
            if i < n and j < n:
                out[n] = phi[i][j] % q
            elif i == n and j < n:
                out[j] = 1
            elif j == n and i < n:
                out[i] = 1
            C[i][j] = tuple(out)
    return C


# ---------------------------------------------------------------- closed forms (Section 4)

def lambda_field(q, k):
    """Squaring in F_(q^k): Lambda = q - q^(1-k)."""
    return q - q ** (1 - k)


def lambda_truncated(q, k):
    """F_q[s]/(s^k) with L = R_l: Lambda = q h, h as in Proposition 63."""
    m = (k + 1) // 2
    lg = math.log2(q)
    h = sum((1 - 1 / q) * q ** (-j) * (1 + j * lg) for j in range(m))
    h += q ** (-m) * (k - m) * lg
    return q * h


def lambda_square_zero(q, m):
    """F_q[s_1..s_m]/(s_i s_j): Lambda = q - 1 + m log2 q."""
    return q - 1 + m * math.log2(q)
