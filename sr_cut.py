# SPDX-License-Identifier: Apache-2.0
# MV2 of Munim, Inc. Made with AI agents working in MV2's name.
"""sr_cut.py -- peeling, cutting and rank expansion for the frame square-root
entropy conjecture SR* (note notes/a177.md).

Frame map of a matrix M over F_q (q odd):  F(y) = y o y + M y,  (y o y)_i = y_i^2.
H(M) = H(Y | F(Y)) in bits, Y uniform on F_q^k.  SR*: H(M) <= k (1 - 1/q).
Exact form: W(M) = prod_y N_y (N_y = size of the fibre of y), H(M) = log2 W(M) / q^k.

Self-contained (standard library only).  In this code q must be an odd PRIME
(the statements of a177 hold for every odd prime power q).
"""
import itertools
import math
from fractions import Fraction


# ---------------------------------------------------------------- basic maps

def points(q, k):
    return list(itertools.product(range(q), repeat=k))


def frame_value(q, M, y):
    k = len(y)
    return tuple((y[i] * y[i] + sum(M[i][j] * y[j] for j in range(k))) % q
                 for i in range(k))


def fibre_sizes(q, M):
    """[N_y for y in points(q, k)], N_y = #{z : F(z) = F(y)}."""
    k = len(M)
    vals = [frame_value(q, M, y) for y in points(q, k)]
    cnt = {}
    for v in vals:
        cnt[v] = cnt.get(v, 0) + 1
    return [cnt[v] for v in vals]


def weight(q, M):
    """Exact integer W(M) = prod_y N_y, so H(M) = log2 W(M) / q^k.  W = 1 for k = 0."""
    if len(M) == 0:
        return 1
    W = 1
    for n in fibre_sizes(q, M):
        W *= n
    return W


def entropy(q, M):
    k = len(M)
    if k == 0:
        return 0.0
    return sum(math.log2(n) for n in fibre_sizes(q, M)) / q ** k


def sub(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]


def shift_diag(q, M, t):
    k = len(M)
    return [[(M[i][j] + (t if i == j else 0)) % q for j in range(k)] for i in range(k)]


# ---------------------------------------------------------------- linear algebra mod q

def rank_mod(A, q):
    A = [[x % q for x in r] for r in A]
    if not A or not A[0]:
        return 0
    nr, nc = len(A), len(A[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if A[i][c]:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], q - 2, q)
        A[r] = [(x * inv) % q for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c]:
                f = A[i][c]
                A[i] = [(a - f * b) % q for a, b in zip(A[i], A[r])]
        r += 1
        if r == nr:
            break
    return r


def in_rowspace(A, v, q):
    if all(x % q == 0 for x in v):
        return True
    if not A:
        return False
    return rank_mod(A + [list(v)], q) == rank_mod(A, q)


# ---------------------------------------------------------------- Lemma 139: peeling

def step_kind(q, M, K, i):
    """Kind of the step that reveals coordinate i after the set K (Lemma 139):
    'lin'  if e_i lies in the row space R of M[K, U], U = complement of K;
    'quad' if rho_i + alpha e_i lies in R for some alpha (rho_i = row i on U, entry i zeroed);
    'free' otherwise."""
    k = len(M)
    U = [j for j in range(k) if j not in K]
    R = [[M[r][j] for j in U] for r in sorted(K)]
    e = [1 if j == i else 0 for j in U]
    if in_rowspace(R, e, q):
        return 'lin'
    for alpha in range(q):
        v = [alpha if j == i else M[i][j] for j in U]
        if in_rowspace(R, v, q):
            return 'quad'
    return 'free'


def peel_counts(q, M, order):
    """(free, quad, lin) step counts of a peeling order (Lemma 139)."""
    K = set()
    f = u = l = 0
    for i in order:
        kind = step_kind(q, M, K, i)
        if kind == 'free':
            f += 1
        elif kind == 'quad':
            u += 1
        else:
            l += 1
        K.add(i)
    return f, u, l


def peel_cost(q, f, u):
    return f * math.log2(q) + u * (1.0 - 1.0 / q)


def peel_bound_holds_exactly(q, M, f, u):
    """Exact check of log2 W(M) <= q^k (f log2 q + u (1 - 1/q)), i.e.
    W^q <= q^(f q^(k+1)) 2^(u (q-1) q^k)."""
    k = len(M)
    return weight(q, M) ** q <= q ** (f * q ** (k + 1)) * 2 ** (u * (q - 1) * q ** k)


def closure(q, M, S):
    """Linear closure of S (Corollary 139.1): add every coordinate whose step is 'lin'."""
    k = len(M)
    K = set(S)
    changed = True
    while changed:
        changed = False
        for i in range(k):
            if i not in K and step_kind(q, M, K, i) == 'lin':
                K.add(i)
                changed = True
    return K


def determined_by(q, M, S):
    """True iff y -> (F(y), y_S) is injective on F_q^k."""
    k = len(M)
    seen = set()
    for y in points(q, k):
        key = (frame_value(q, M, y), tuple(y[i] for i in sorted(S)))
        if key in seen:
            return False
        seen.add(key)
    return True


# ---------------------------------------------------------------- Theorem 63: bands

def is_upper_band(q, M, w):
    """M[i][j] = 0 for j > i + w and M[i][i+w] != 0 for all i < k - w (0-based)."""
    k = len(M)
    for i in range(k):
        for j in range(k):
            if j > i + w and M[i][j] % q:
                return False
        if i + w < k and M[i][i + w] % q == 0:
            return False
    return True


# ---------------------------------------------------------------- Lemma 140: cut

def cut_rank(q, M, S):
    """min(rank M[S, S^c], rank M[S^c, S]) (Lemma 140)."""
    k = len(M)
    S = sorted(S)
    Sc = [i for i in range(k) if i not in S]
    if not S or not Sc:
        return 0
    return min(rank_mod(sub(M, S, Sc), q), rank_mod(sub(M, Sc, S), q))


def cut_bound_holds_exactly(q, M, S):
    """Exact check of H(M) <= H(M_SS) + H(M_ScSc) + cut_rank log2 q, i.e.
    W(M) <= W(M_SS)^(q^|Sc|) W(M_ScSc)^(q^|S|) q^(cut_rank q^k)."""
    k = len(M)
    S = sorted(S)
    Sc = [i for i in range(k) if i not in S]
    lhs = weight(q, M)
    rhs = (weight(q, sub(M, S, S)) ** (q ** len(Sc)) *
           weight(q, sub(M, Sc, Sc)) ** (q ** len(S)) *
           q ** (cut_rank(q, M, S) * q ** k))
    return lhs <= rhs


# ---------------------------------------------------------------- Theorem 64: rank expansion

def rho(q, M, T):
    """rank of M[T^c, T] (rows outside T, columns in T)."""
    k = len(M)
    T = sorted(T)
    Tc = [i for i in range(k) if i not in T]
    if not T or not Tc:
        return 0
    return rank_mod(sub(M, Tc, T), q)


def mean_fibre(q, M):
    k = len(M)
    return Fraction(sum(fibre_sizes(q, M)), q ** k)


def pair_count_mean(q, M):
    """a174 Theorem 58: E N = sum_d q^(-w(d)) [ (M d)_i = 0 for every i outside supp d ]."""
    k = len(M)
    tot = Fraction(0)
    for d in points(q, k):
        if all(sum(M[i][j] * d[j] for j in range(k)) % q == 0 for i in range(k) if d[i] == 0):
            tot += Fraction(1, q ** sum(1 for x in d if x))
    return tot


def expansion_sum(q, M):
    """sum_T ((q-1)/q)^|T| (q-1)^(-rho(T)), an upper bound for E N (Theorem 64)."""
    k = len(M)
    s = Fraction(0)
    for t in range(k + 1):
        for T in itertools.combinations(range(k), t):
            s += Fraction((q - 1) ** t, q ** t * (q - 1) ** rho(q, M, T))
    return s


def half_expanding(q, M):
    """rho(T) >= ceil(min(|T|, k - |T|) / 2) for every T (hypothesis of Theorem 64)."""
    k = len(M)
    for t in range(1, k):
        need = (min(t, k - t) + 1) // 2
        for T in itertools.combinations(range(k), t):
            if rho(q, M, T) < need:
                return False
    return True


def ratios(q):
    """r1 = (1 + a/c)/b, r2 = (a + 1/c)/b with a = (q-1)/q, c = sqrt(q-1), b = 2^(1-1/q)."""
    a = (q - 1) / q
    c = math.sqrt(q - 1)
    b = 2.0 ** (1.0 - 1.0 / q)
    return (1.0 + a / c) / b, (a + 1.0 / c) / b


def sr_strict_holds_exactly(q, M):
    """Exact check of H(M) < k (1 - 1/q):  W^q < 2^(k (q-1) q^k)."""
    k = len(M)
    return weight(q, M) ** q < 2 ** (k * (q - 1) * q ** k)


def generic_failure_bound(q, k):
    """Corollary 64.1: P(uniform M is not half-expanding) <= 4x/(1-x), x = k q^(-k/8)."""
    x = k * q ** (-k / 8.0)
    return 4 * x / (1 - x) if x < 1 else float('inf')
