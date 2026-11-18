"""twocodes.py -- helpers for note a175 (frames: the rank identity and the two-code criterion).

MV2 of Munim, Inc. (mv2@munimtech.com). Licensed under the Apache License, Version 2.0
(Apache-2.0). Made with AI agents working in MV2's name. Standard library only, self-contained.
In this module q is always a PRIME (arithmetic is mod q).

Notation (note a175):
  S(y)      = y o y, (y o y)_i = y_i^2 (the frame square)
  frame map F(y) = y o y + M y on F_q^k;  H(M) = H(Y | F(Y)) in bits, Y uniform on F_q^k
  M = U V^T with U, V in F_q^(k x r) (rows indexed by the k coordinates)
  tau(y)    = V^T y in F_q^r
  W_A(x)    = sum over c in F_q^r of x^(w(A c)), w = Hamming weight (A in F_q^(k x r))
  theta     = (q + 1) / (2q)
"""
import itertools
import math
from collections import Counter, defaultdict
from fractions import Fraction


# ----------------------------------------------------------------------------- basics
def all_points(q, k):
    return list(itertools.product(range(q), repeat=k))


def cond_entropy(points, f, g):
    """H(f(Y) | g(Y)) in bits for Y uniform on `points`."""
    joint = Counter((g(y), f(y)) for y in points)
    marg = Counter(g(y) for y in points)
    n = len(points)
    h = 0.0
    for (b, _a), c in joint.items():
        h -= (c / n) * math.log2(c / marg[b])
    return h


def ident(y):
    return tuple(y)


def square_map(q):
    def S(y):
        return tuple((x * x) % q for x in y)
    return S


def frame_map(q, M):
    k = len(M)

    def F(y):
        return tuple((y[i] * y[i] + sum(M[i][j] * y[j] for j in range(k))) % q
                     for i in range(k))
    return F


def lin_map(q, A):
    """y -> A^T y in F_q^r, for A in F_q^(k x r)."""
    k, r = len(A), len(A[0])

    def T(y):
        return tuple(sum(A[i][l] * y[i] for i in range(k)) % q for l in range(r))
    return T


def uvT(q, U, V):
    """M = U V^T, M[i][j] = sum_l U[i][l] V[j][l], so M y = U (V^T y)."""
    k, r = len(U), len(U[0])
    return [[sum(U[i][l] * V[j][l] for l in range(r)) % q for j in range(k)]
            for i in range(k)]


def frame_entropy(q, M):
    return cond_entropy(all_points(q, len(M)), ident, frame_map(q, M))


def rank_mod(rows, q):
    """Rank of a matrix (list of rows) over GF(q), q prime. Empty matrices have rank 0."""
    A = [list(r) for r in rows]
    if not A or not A[0]:
        return 0
    nr, nc = len(A), len(A[0])
    r = 0
    for c in range(nc):
        piv = None
        for i in range(r, nr):
            if A[i][c] % q:
                piv = i
                break
        if piv is None:
            continue
        A[r], A[piv] = A[piv], A[r]
        inv = pow(A[r][c], q - 2, q)
        A[r] = [(x * inv) % q for x in A[r]]
        for i in range(nr):
            if i != r and A[i][c] % q:
                f = A[i][c]
                A[i] = [(a - f * b) % q for a, b in zip(A[i], A[r])]
        r += 1
        if r == nr:
            break
    return r


def reach(M, s):
    k = len(M)
    seen = {s}
    stack = [s]
    while stack:
        i = stack.pop()
        for j in range(k):
            if j != i and M[i][j] and j not in seen:
                seen.add(j)
                stack.append(j)
    return seen


def strongly_connected(M):
    """Is the off-diagonal digraph of M (edge i -> j iff i != j and M[i][j] != 0) strongly
    connected?"""
    k = len(M)
    if reach(M, 0) != set(range(k)):
        return False
    MT = [[M[j][i] for j in range(k)] for i in range(k)]
    return reach(MT, 0) == set(range(k))


# ----------------------------------------------------------------------------- codes
def weight_hist(q, A):
    """Counter {w : #{c in F_q^r : w(A c) = w}} for A in F_q^(k x r)."""
    k, r = len(A), len(A[0])
    cols = [[A[i][l] for i in range(k)] for l in range(r)]
    hist = Counter()

    def rec(l, vec):
        if l == r:
            hist[sum(1 for x in vec if x)] += 1
            return
        col = cols[l]
        rec(l + 1, vec)
        for a in range(1, q):
            rec(l + 1, [(v + a * c) % q for v, c in zip(vec, col)])

    rec(0, [0] * k)
    return hist


def enumerator(hist, x):
    """W(x) = sum_w A_w x^w, exact."""
    x = Fraction(x)
    return sum(Fraction(n) * x ** w for w, n in hist.items())


def W(q, A, x):
    return enumerator(weight_hist(q, A), x)


def theta(q):
    return Fraction(q + 1, 2 * q)


def chi(q, a):
    """Quadratic character of GF(q), chi(0) = 0."""
    a %= q
    if a == 0:
        return 0
    return 1 if pow(a, (q - 1) // 2, q) == 1 else -1


def compat_sum(q, U):
    """sum_{c in F_q^r} prod_{i : (U c)_i != 0} (q + chi(-(U c)_i)) / (2q), exact (Lemma 133)."""
    k, r = len(U), len(U[0])
    tot = Fraction(0)
    for c in itertools.product(range(q), repeat=r):
        p = Fraction(1)
        for i in range(k):
            a = sum(U[i][l] * c[l] for l in range(r)) % q
            if a:
                p *= Fraction(q + chi(q, -a), 2 * q)
        tot += p
    return tot


# ----------------------------------------------------------------------------- note a175
def mean_compatible(q, U, V):
    """E_Y K(Y), K(y) = #{tau(z) : F(z) = F(y)}, F the frame map of M = U V^T (exact)."""
    k = len(U)
    F = frame_map(q, uvT(q, U, V))
    T = lin_map(q, V)
    pts = all_points(q, k)
    seen = defaultdict(set)
    for y in pts:
        seen[F(y)].add(T(y))
    return Fraction(sum(len(seen[F(y)]) for y in pts), len(pts))


def collision_given_square(q, V):
    """E_S sum_x P(tau = x | S)^2, exact (Lemma 134 says it equals W_V(1/2) / q^r)."""
    k = len(V)
    T = lin_map(q, V)
    S = square_map(q)
    groups = defaultdict(Counter)
    for y in all_points(q, k):
        groups[S(y)][T(y)] += 1
    n = q ** k
    tot = Fraction(0)
    for cnt in groups.values():
        g = sum(cnt.values())
        tot += Fraction(g, n) * sum(Fraction(c, g) ** 2 for c in cnt.values())
    return tot


def sign_fourier(q, a):
    """E_S |E[omega^(a Y) | S]|^2 for Y uniform on F_q, S = Y^2 (Lemma 134: it is 1/2)."""
    tot = 0.0
    for y in range(q):
        roots = [z for z in range(q) if (z * z - y * y) % q == 0]
        for z in roots:
            tot += math.cos(2 * math.pi * a * (y - z) / q) / len(roots)
    return tot / q


def theorem60_bound(q, U, V):
    """k(1 - 1/q) - r log2 q + log2 W_U(theta) + log2 W_V(1/2)."""
    k, r = len(U), len(U[0])
    return (k * (q - 1) / q - r * math.log2(q)
            + math.log2(W(q, U, theta(q))) + math.log2(W(q, V, Fraction(1, 2))))


def column_worst(q, r):
    """a_q^r with a_q = 1 + (q - 1) theta = (q^2 + 2q - 1)/(2q): max of W_U(theta), rank r."""
    return (1 + (q - 1) * theta(q)) ** r


# ----------------------------------------------------------------------------- certificate
def lcg(seed):
    """A fixed 64-bit linear congruential generator (reproducible on every platform)."""
    x = seed % (1 << 64)
    while True:
        x = (6364136223846793005 * x + 1442695040888963407) % (1 << 64)
        yield x >> 33


def certificate_U(r, k):
    """Rows 0..r-1 = e_0..e_(r-1); rows r..k-1 = e_0 (a column code with many light words)."""
    U = [[1 if l == i else 0 for l in range(r)] for i in range(r)]
    U += [[1] + [0] * (r - 1) for _ in range(k - r)]
    return U


def certificate_instance(q=3, r=11, k=28, max_seed=10):
    """First seed s >= 1 for which V (entries next(lcg(s)) mod q, row by row) gives M = U V^T
    of rank r, strongly connected, with 2 W_U(theta) W_V(1/2) <= q^r (so Theorem 60 leaves a
    margin of at least one bit). Returns (seed, U, V, M, WU, WV) or None."""
    U = certificate_U(r, k)
    WU = W(q, U, theta(q))
    for seed in range(1, max_seed + 1):
        g = lcg(seed)
        V = [[next(g) % q for _ in range(r)] for _ in range(k)]
        M = uvT(q, U, V)
        if rank_mod(M, q) != r or not strongly_connected(M):
            continue
        WV = W(q, V, Fraction(1, 2))
        if 2 * WU * WV <= q ** r:
            return seed, U, V, M, WU, WV
    return None
