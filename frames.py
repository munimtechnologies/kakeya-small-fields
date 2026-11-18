"""frames.py -- helpers for note a174 (frames with an arbitrary linear part; planar maps).

MV2 of Munim, Inc. (mv2@munimtech.com). Licensed under the Apache License, Version 2.0
(Apache-2.0). Made with AI agents working in MV2's name. Standard library only, self-contained.
In this module q is always a PRIME (arithmetic is mod q); F_(q^k) is built by polynomials.

Notation (note a174):
  frame map      F(y) = y o y + M y on F_q^k, (y o y)_i = y_i^2
  H(M)           = H(Y | F(Y)) in bits, Y uniform on F_q^k
  edge i -> j    iff i != j and M[i][j] != 0 (output i depends on input j)
"""
import itertools
import math
from collections import Counter
from fractions import Fraction


# ----------------------------------------------------------------------------- basics
def all_points(q, k):
    return list(itertools.product(range(q), repeat=k))


def fibre_entropy(points, F):
    """H(Y | F(Y)) in bits for Y uniform on `points`."""
    cnt = Counter(F(y) for y in points)
    return sum(c * math.log2(c) for c in cnt.values()) / len(points)


def fibre_sizes(points, F):
    img = {y: F(y) for y in points}
    cnt = Counter(img.values())
    return {y: cnt[img[y]] for y in points}


def mean_fibre(points, F):
    """E_Y N(Y) = (number of pairs with equal image) / |points|, exact."""
    cnt = Counter(F(y) for y in points)
    return Fraction(sum(c * c for c in cnt.values()), len(points))


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


# ----------------------------------------------------------------------------- frames
def frame_map(q, M):
    k = len(M)

    def F(y):
        return tuple((y[i] * y[i] + sum(M[i][j] * y[j] for j in range(k))) % q
                     for i in range(k))
    return F


def frame_entropy(q, M):
    return fibre_entropy(all_points(q, len(M)), frame_map(q, M))


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


def sccs(M):
    """Strongly connected components of the off-diagonal digraph of M."""
    k = len(M)
    R = [reach(M, i) for i in range(k)]
    comps, done = [], set()
    for i in range(k):
        if i in done:
            continue
        comp = sorted(j for j in R[i] if i in R[j])
        comps.append(comp)
        done.update(comp)
    return comps


def strongly_connected(M):
    return len(sccs(M)) == 1


def submatrix(M, rows, cols):
    return [[M[i][j] for j in cols] for i in rows]


def pair_formula(q, M):
    """Theorem 58 identity: sum over d of q^(-|supp d|) [ (Md)_i = 0 for every i off supp d ]."""
    k = len(M)
    tot = Fraction(0)
    for d in itertools.product(range(q), repeat=k):
        ok = True
        for i in range(k):
            if d[i] == 0 and sum(M[i][j] * d[j] for j in range(k)) % q:
                ok = False
                break
        if ok:
            tot += Fraction(1, q ** sum(1 for x in d if x))
    return tot


def V_count(q, M, T):
    """V(T) = #{d : supp d = T, M_(T^c, T) d_T = 0}."""
    k = len(M)
    Tc = [i for i in range(k) if i not in T]
    n = 0
    for dT in itertools.product(range(1, q), repeat=len(T)):
        if all(sum(M[i][T[a]] * dT[a] for a in range(len(T))) % q == 0 for i in Tc):
            n += 1
    return n


def phi_bound(q, k):
    """Phi_q(k): Jensen bound on E N for a strongly connected frame of size k >= 2."""
    a = (q - 1) / q
    return (q - 2) / (q - 1) * (1 + a ** k) + (2 - 1 / q) ** k / (q - 1)


def K0(q, kmax=1000):
    """Largest K with log2 Phi_q(k) < k(q-1)/q for every 2 <= k <= K."""
    for k in range(2, kmax + 1):
        if not math.log2(phi_bound(q, k)) < k * (q - 1) / q:
            return k - 1
    raise ValueError("kmax too small")


def scc_bound(q, M):
    """Sum over SCCs C of h(|C|): (q-1)/q for singletons, log2 Phi_q(|C|) otherwise."""
    tot = 0.0
    for C in sccs(M):
        tot += (q - 1) / q if len(C) == 1 else math.log2(phi_bound(q, len(C)))
    return tot


# ----------------------------------------------------------------------------- low rank
def uvT(q, U, V):
    k, r = len(U), len(U[0])
    return [[sum(U[i][l] * V[j][l] for l in range(r)) % q for j in range(k)] for i in range(k)]


def find_J(q, V):
    k, r = len(V), len(V[0])
    for J in itertools.combinations(range(k), r):
        if rank_mod([V[i] for i in J], q) == r:
            return list(J)
    return None


def low_rank_B(q, U, J):
    """B_J = sum_{tau != 0} q^(-w_J(U tau)) theta^(w_{J^c}(U tau)), theta = (q+1)/(2q)."""
    k, r = len(U), len(U[0])
    theta = (q + 1) / (2 * q)
    B = 0.0
    for tau in itertools.product(range(q), repeat=r):
        if not any(tau):
            continue
        Ut = [sum(U[i][l] * tau[l] for l in range(r)) % q for i in range(k)]
        wJ = sum(1 for i in J if Ut[i])
        wC = sum(1 for i in range(k) if i not in J and Ut[i])
        B += q ** (-wJ) * theta ** wC
    return B


def low_rank_bound(q, U, J):
    k, r = len(U), len(U[0])
    return (k - r) * (q - 1) / q + math.log2(1 + low_rank_B(q, U, J))


def root_count(q, y, c):
    """#{x in F_q : x^2 - 2 y x = c}."""
    return sum(1 for x in range(q) if (x * x - 2 * y * x - c) % q == 0)


def beta_pointwise(q, U, J, yC, C):
    """beta = sum_{tau != 0} q^(-w_J(U tau)) prod_{i in J^c} |R_i(tau)| (exact Fraction).
    yC[a] is the value of y at coordinate C[a]."""
    r = len(U[0])
    tot = Fraction(0)
    for tau in itertools.product(range(q), repeat=r):
        if not any(tau):
            continue
        Ut = [sum(U[i][l] * tau[l] for l in range(r)) % q for i in range(len(U))]
        wJ = sum(1 for i in J if Ut[i])
        prod = 1
        for a, i in enumerate(C):
            prod *= root_count(q, yC[a], Ut[i])
        tot += Fraction(prod, q ** wJ)
    return tot


def zero_sum_subsets(q, y, v):
    """Z(y) = #{T subset of supp y : sum_{i in T} v_i y_i = 0}."""
    S = [i for i in range(len(y)) if y[i]]
    n = 0
    for m in range(len(S) + 1):
        for T in itertools.combinations(S, m):
            if sum(v[i] * y[i] for i in T) % q == 0:
                n += 1
    return n


# ----------------------------------------------------------------------------- algebras
def algebra_mul(C, q):
    """C[i][j] = coordinates of e_i o e_j."""
    k = len(C)

    def mul(x, y):
        out = [0] * k
        for i in range(k):
            if x[i]:
                for j in range(k):
                    if y[j]:
                        c = x[i] * y[j]
                        cij = C[i][j]
                        for l in range(k):
                            out[l] += c * cij[l]
        return tuple(v % q for v in out)
    return mul


def R_matrix(C, d, q):
    k = len(C)
    return [[sum(d[i] * C[i][j][l] for i in range(k)) % q for j in range(k)] for l in range(k)]


def rho(C, q):
    """rho(B) = sum_d q^(-rank R_d) (Theorem 57)."""
    k = len(C)
    return sum(Fraction(1, q ** rank_mod(R_matrix(C, d, q), q))
               for d in itertools.product(range(q), repeat=k))


def is_planar(C, q):
    k = len(C)
    return all(rank_mod(R_matrix(C, d, q), q) == k
               for d in itertools.product(range(q), repeat=k) if any(d))


def slice_map(C, L, t, q):
    k = len(C)
    mul = algebra_mul(C, q)

    def A(x):
        s = mul(x, x)
        return tuple((s[i] + sum(L[i][j] * x[j] for j in range(k)) + t * x[i]) % q
                     for i in range(k))
    return A


def Lambda(C, L, q):
    pts = all_points(q, len(C))
    return sum(fibre_entropy(pts, slice_map(C, L, t, q)) for t in range(q))


# ----------------------------------------------------------------------------- GF(p^k)
def poly_mulmod(a, b, f, p):
    """a, b: coefficient tuples of length k (low degree first); f: monic, length k+1."""
    k = len(a)
    prod = [0] * (2 * k - 1)
    for i in range(k):
        if a[i]:
            for j in range(k):
                prod[i + j] += a[i] * b[j]
    for deg in range(2 * k - 2, k - 1, -1):
        c = prod[deg] % p
        if c:
            for s in range(k + 1):
                prod[deg - k + s] -= c * f[s]
    return tuple(x % p for x in prod[:k])


def irreducible_poly(p, k):
    """A monic irreducible polynomial of degree 2 or 3 over GF(p) (no roots)."""
    assert k in (2, 3)
    for coeffs in itertools.product(range(p), repeat=k):
        f = list(coeffs) + [1]
        if all(sum(f[s] * pow(x, s, p) for s in range(k + 1)) % p for x in range(p)):
            return f
    raise ValueError


def field_structure(p, k, twist=0):
    """Structure constants of F_(p^k) as an F_p-algebra.
    twist = 0: ordinary multiplication x*y (unit 1, squaring map).
    twist = i > 0: x o y = x^(p^i) y + x y^(p^i) (Albert's twisted product; F_p-bilinear)."""
    f = irreducible_poly(p, k)
    basis = [tuple(1 if s == i else 0 for s in range(k)) for i in range(k)]

    def mul(a, b):
        return poly_mulmod(a, b, f, p)

    def power(a, e):
        r = tuple(1 if s == 0 else 0 for s in range(k))
        for _ in range(e):
            r = mul(r, a)
        return r

    C = [[None] * k for _ in range(k)]
    for i in range(k):
        for j in range(k):
            if twist == 0:
                C[i][j] = mul(basis[i], basis[j])
            else:
                e = p ** twist
                u = mul(power(basis[i], e), basis[j])
                w = mul(basis[i], power(basis[j], e))
                C[i][j] = tuple((u[s] + w[s]) % p for s in range(k))
    return C
