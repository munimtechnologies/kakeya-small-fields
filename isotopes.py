"""Isotopes, spin factors and the spectral lemma for quadratic Kakeya maps (note a173).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only; this module imports no other repo module.

A commutative algebra A of dimension k over F_q (q an odd prime here) is given by structure
constants C[i][j] = e_i o e_j (a k-tuple), symmetric in i, j. A quadratic map is
P(x) = x o x + L x + c. For a map P let A_t(x) = P(x) + t x and

    Lambda(P) = sum_t H(X | A_t(X)),     X uniform on F_q^k (bits).
"""
import itertools
import math
from collections import Counter


# ---------------------------------------------------------------- linear algebra mod q

def unit_vec(k, j):
    return tuple(1 if i == j else 0 for i in range(k))


def identity(k):
    return [[1 if i == j else 0 for j in range(k)] for i in range(k)]


def mat_vec(M, x, q):
    return tuple(sum(M[i][j] * x[j] for j in range(len(x))) % q for i in range(len(M)))


def mat_add(A, B, q):
    return [[(a + b) % q for a, b in zip(ra, rb)] for ra, rb in zip(A, B)]


def mat_scale(A, s, q):
    return [[a * s % q for a in row] for row in A]


def mat_mul(A, B, q):
    k = len(B[0])
    return [[sum(A[i][m] * B[m][j] for m in range(len(B))) % q for j in range(k)]
            for i in range(len(A))]


def mat_inv(M, q):
    """Inverse of a square matrix over F_q (q prime), or None if singular."""
    k = len(M)
    A = [[x % q for x in M[i]] + [1 if i == j else 0 for j in range(k)] for i in range(k)]
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
        A[col] = [v * inv % q for v in A[col]]
        for r in range(k):
            if r != col and A[r][col]:
                f = A[r][col]
                A[r] = [(a - f * b) % q for a, b in zip(A[r], A[col])]
    return [row[k:] for row in A]


# ---------------------------------------------------------------- algebras and maps

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
            for m in range(k):
                if row[m]:
                    out[m] = (out[m] + c * row[m]) % q
    return tuple(out)


def square(C, x, q):
    return mult(C, x, x, q)


def mult_matrix(C, a, q):
    """Matrix of R_a : x -> a o x (column j is a o e_j)."""
    k = len(a)
    cols = [mult(C, a, unit_vec(k, j), q) for j in range(k)]
    return [[cols[j][i] for j in range(k)] for i in range(k)]


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


def cond_entropy(F, q, k):
    """H(X | F(X)) for X uniform on F_q^k."""
    cnt = Counter(F(x) for x in all_vectors(q, k))
    return sum(m * math.log2(m) for m in cnt.values()) / q ** k


def fibre_sizes(F, q, k):
    pts = all_vectors(q, k)
    img = [F(x) for x in pts]
    cnt = Counter(img)
    return sorted(cnt[v] for v in img)


def shifted(P, q, t):
    def A(x):
        y = P(x)
        return tuple((y[i] + t * x[i]) % q for i in range(len(x)))
    return A


def lambda_terms(P, q, k):
    return [cond_entropy(shifted(P, q, t), q, k) for t in range(q)]


def kakeya_lambda(P, q, k):
    return sum(lambda_terms(P, q, k))


def is_unit(C, e, q):
    k = len(C)
    return all(mult(C, e, unit_vec(k, j), q) == unit_vec(k, j) for j in range(k))


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


def random_commutative(q, k, rng):
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(i, k):
            v = tuple(rng.randrange(q) for _ in range(k))
            C[i][j] = v
            C[j][i] = v
    return C


def random_matrix(q, k, rng):
    return [[rng.randrange(q) for _ in range(k)] for _ in range(k)]


# ---------------------------------------------------------------- Theorem 54: isotopes

def regular_point(C, q):
    """Some p in F_q^k with R_p invertible, or None if the algebra is not regular."""
    k = len(C)
    for p in all_vectors(q, k):
        if mat_inv(mult_matrix(C, p, q), q) is not None:
            return p
    return None


def isotope(C, p, q):
    """x * y = R_p^{-1}(x o y). Commutative, with unit p (R_p must be invertible)."""
    k = len(C)
    Rinv = mat_inv(mult_matrix(C, p, q), q)
    D = [[mat_vec(Rinv, C[i][j], q) for j in range(k)] for i in range(k)]
    return D, Rinv


def slice_as_unital(C, L, c, p, q, t):
    """The unital map x -> x * x + R_p^{-1}(L + t I) x + R_p^{-1} c of Theorem 54."""
    k = len(C)
    D, Rinv = isotope(C, p, q)
    M = mat_mul(Rinv, mat_add(L, mat_scale(identity(k), t, q), q), q)
    return D, M, mat_vec(Rinv, c, q)


# ---------------------------------------------------------------- Theorem 55: spin factors

def spin_factor(q, Phi):
    """J(V, phi): basis e_0 = 1, e_1..e_n spanning V; v o w = phi(v, w) 1.
    Phi is a symmetric n x n matrix (any rank, degenerate allowed)."""
    n = len(Phi)
    k = n + 1
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if i == 0:
                C[i][j] = unit_vec(k, j)
            elif j == 0:
                C[i][j] = unit_vec(k, i)
            else:
                C[i][j] = tuple((Phi[i - 1][j - 1] % q) if m == 0 else 0 for m in range(k))
    return C


def quad_value(Phi, w, q):
    n = len(w)
    return sum(Phi[i][j] * w[i] * w[j] for i in range(n) for j in range(n)) % q


def nonzero_squares(q):
    return sorted({x * x % q for x in range(1, q)})


def spin_formula(q, Phi):
    """H(Y | Y^2) on J(V, phi) by the case analysis of Section 3 of a173 (no use of J)."""
    n = len(Phi)
    N = Counter(quad_value(Phi, w, q) for w in all_vectors(q, n))
    sq = set(nonzero_squares(q))
    S = sum(N[p] for p in sq)
    total = (q ** n - 1) * (q - 1) + (q - 3) * S
    total += sum(2 * math.log2(2 + N[c]) for c in sq)
    for p in range(q):
        if N[p]:
            total += N[p] * math.log2(N[p] + (2 if p in sq else 0))
    return total / q ** (n + 1)


def spin_crude_bound(q, n):
    """G(q, n) of Section 3: q H(Y | Y^2) <= G(q, n) for every spin factor of dimension n + 1."""
    u = float(q) ** (-n)
    return ((2 * q - 4) * (1 - u) + (q - 1) * u * math.log2(q ** n + 1)
            + math.log2(q ** n + 2))


def symmetric_matrices(q, n):
    idx = [(i, j) for i in range(n) for j in range(i, n)]
    for vals in itertools.product(range(q), repeat=len(idx)):
        M = [[0] * n for _ in range(n)]
        for (i, j), v in zip(idx, vals):
            M[i][j] = v
            M[j][i] = v
        yield M


def random_symmetric(q, n, rng):
    M = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i, n):
            v = rng.randrange(q)
            M[i][j] = v
            M[j][i] = v
    return M


# ---------------------------------------------------------------- Theorem 56: spectral lemma

def spectral_set(C, L, q):
    """T = {t : -t is an F_q-eigenvalue of R_u + L for some u}."""
    k = len(C)
    T = set()
    pts = all_vectors(q, k)
    nonzero = [d for d in pts if any(d)]
    for u in pts:
        M = mat_add(mult_matrix(C, u, q), L, q)
        for d in nonzero:
            Md = mat_vec(M, d, q)
            i = next(a for a in range(k) if d[a])
            lam = Md[i] * pow(d[i], q - 2, q) % q
            if all((Md[a] - lam * d[a]) % q == 0 for a in range(k)):
                T.add((-lam) % q)
    return T


def flag_nilpotent(q, k, rng):
    """Random commutative algebra with e_i o e_j in span(e_m : m > max(i, j))."""
    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(i, k):
            lo = max(i, j) + 1
            v = tuple(rng.randrange(q) if m >= lo else 0 for m in range(k))
            C[i][j] = v
            C[j][i] = v
    return C


def flag_lowering(q, k, rng):
    """Random L with L e_j in span(e_m : m > j) (strictly lower triangular)."""
    return [[rng.randrange(q) if i > j else 0 for j in range(k)] for i in range(k)]


def power_failure_example():
    """k = 4: e0 o e0 = e1, e0 o e1 = e2, e1 o e1 = e3, other products 0. Flag-nilpotent and
    not power-associative: x = e0 has x^2 o x^2 = e3 but (x^2 o x) o x = 0."""
    k = 4
    C = [[(0,) * k for _ in range(k)] for _ in range(k)]
    C[0][0] = unit_vec(k, 1)
    C[0][1] = C[1][0] = unit_vec(k, 2)
    C[1][1] = unit_vec(k, 3)
    return C


# ---------------------------------------------------------------- G_n of a167

def g_map_algebra(q, phi):
    """a167's G_n: (u, s) o (w, t) = (s w + t u, phi(u, w)); basis u-part, then s."""
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
