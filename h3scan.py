# SPDX-License-Identifier: Apache-2.0
"""h3scan.py - reference code for the exhaustive h_3 scans over F_3 (notes/prereg-h3scan.md).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only.

For a map P: F_3^3 -> F_3^3 let F_t(x) = P(x) + t x (t = 0, 1, 2) and

    S(P) = sum_t sum_{fibres F of F_t} |F| log2 |F|      (= 27 Lambda(P) of note a164).

README Theorem 2: h_3 = 3 log2 3 - max_P S(P) / 81, and the F_3 Kakeya growth base is at
most 2^(h_3/3) = 3 * 2^(-S/243). KLSS's base 1.889882 = 3 * 2^(-2/3) corresponds to S = 162.
A single map with S(P) > 162 would give a new record upper bound (Conjecture C_3(3) of a164
says this never happens). Exact test: S(P) > 162 iff prod_t prod_F |F|^|F| > 2^162.

Families scanned by h3scan.c (all exhaustive):
  quadratic  P = Q + L, Q any vector of three quadratic forms, L any 3x3 matrix
             (L reduced to one representative per class under conjugation and L -> L + lam I);
  s3         every S_3-equivariant map of any degree: P(x)_i = f(x_i, {x_j, x_k});
  cyclic     every Z/3-equivariant map P(x) = (f(x), f(sx), f(s^2 x)), s x = (x2, x3, x1),
             with f of total degree <= 3 (each variable to degree <= 2).
"""
import math

PTS = [(i // 9, (i // 3) % 3, i % 3) for i in range(27)]


def idx(v):
    return 9 * v[0] + 3 * v[1] + v[2]


def digits(n, k):
    return [(n // 3 ** i) % 3 for i in range(k)]


# ---------------------------------------------------------------- scores

def slice_counts(P):
    """List of three dicts value -> fibre size, one for each F_t(x) = P(x) + t x."""
    out = []
    for t in range(3):
        cnt = {}
        for x in range(27):
            v = tuple((P[x][i] + t * PTS[x][i]) % 3 for i in range(3))
            cnt[v] = cnt.get(v, 0) + 1
        out.append(cnt)
    return out


def S_float(P):
    return sum(s * math.log2(s) for c in slice_counts(P) for s in c.values())


def S_exact_power(P):
    """Integer N with S(P) = log2 N exactly."""
    N = 1
    for c in slice_counts(P):
        for s in c.values():
            N *= s ** s
    return N


def compare_162(P):
    """+1 if S(P) > 162, 0 if S(P) == 162, -1 if S(P) < 162 (exact)."""
    N = S_exact_power(P)
    T = 2 ** 162
    return (N > T) - (N < T)


def base_from_S(S):
    """Kakeya growth base 3 * 2^(-S/243) given by a block of length 3 with score S."""
    return 3.0 * 2.0 ** (-S / 243.0)


# ---------------------------------------------------------------- families

def mono6(x):
    x1, x2, x3 = x
    return (x1 * x1 % 3, x2 * x2 % 3, x3 * x3 % 3, x1 * x2 % 3, x1 * x3 % 3, x2 * x3 % 3)


def qform(c, x):
    """Quadratic form number c (0..728): digit i of c is the coefficient of mono6[i]."""
    return sum(a * b for a, b in zip(digits(c, 6), mono6(x))) % 3


def mat_vec(A, v):
    return tuple(sum(A[i][j] * v[j] for j in range(3)) % 3 for i in range(3))


def quad_map(L, c1, c2, c3):
    """P(x) = (q_c1(x), q_c2(x), q_c3(x)) + L x."""
    P = []
    for x in PTS:
        lx = mat_vec(L, x)
        q = (qform(c1, x), qform(c2, x), qform(c3, x))
        P.append(tuple((q[i] + lx[i]) % 3 for i in range(3)))
    return P


def pair_index(a, b):
    a, b = min(a, b), max(a, b)
    return {(0, 0): 0, (0, 1): 1, (0, 2): 2, (1, 1): 3, (1, 2): 4, (2, 2): 5}[(a, b)]


def s3_map(fidx):
    """P(x)_i = f[6 x_i + pair_index(other two coordinates)], digit a of fidx = f[a]."""
    f = digits(fidx, 18)
    P = []
    for x in PTS:
        row = []
        for i in range(3):
            o = [x[j] for j in range(3) if j != i]
            row.append(f[6 * x[i] + pair_index(o[0], o[1])])
        P.append(tuple(row))
    return P


CYC_MONOS = [(a, b, c) for a in range(3) for b in range(3) for c in range(3)
             if 1 <= a + b + c <= 3]


def cyc_f(cidx, y):
    d = digits(cidx, len(CYC_MONOS))
    return sum(dj * (y[0] ** e[0]) * (y[1] ** e[1]) * (y[2] ** e[2])
               for dj, e in zip(d, CYC_MONOS)) % 3


def cyc_map(cidx):
    P = []
    for x in PTS:
        y2 = (x[1], x[2], x[0])
        y3 = (x[2], x[0], x[1])
        P.append((cyc_f(cidx, x), cyc_f(cidx, y2), cyc_f(cidx, y3)))
    return P


# ---------------------------------------------------------------- matrices

def all_matrices():
    for n in range(3 ** 9):
        d = digits(n, 9)
        yield ((d[0], d[1], d[2]), (d[3], d[4], d[5]), (d[6], d[7], d[8]))


def mat_mul(A, B):
    return tuple(tuple(sum(A[i][k] * B[k][j] for k in range(3)) % 3 for j in range(3))
                 for i in range(3))


def det3(A):
    return (A[0][0] * (A[1][1] * A[2][2] - A[1][2] * A[2][1])
            - A[0][1] * (A[1][0] * A[2][2] - A[1][2] * A[2][0])
            + A[0][2] * (A[1][0] * A[2][1] - A[1][1] * A[2][0])) % 3


def mat_inv(A):
    d = det3(A)
    if d == 0:
        raise ValueError("singular")
    dinv = d  # 1*1 = 2*2 = 1 mod 3
    cof = [[0] * 3 for _ in range(3)]
    for i in range(3):
        for j in range(3):
            r = [k for k in range(3) if k != i]
            c = [k for k in range(3) if k != j]
            minor = A[r[0]][c[0]] * A[r[1]][c[1]] - A[r[0]][c[1]] * A[r[1]][c[0]]
            cof[i][j] = ((-1) ** (i + j)) * minor
    # inverse = adj / det, adj = cofactor transpose
    return tuple(tuple((cof[j][i] * dinv) % 3 for j in range(3)) for i in range(3))


def gl3():
    return [A for A in all_matrices() if det3(A) != 0]


def conj_shift_reps():
    """One representative (the least encoding) per class of 3x3 matrices under
    L -> A L A^-1 + lam I; returns list of (rep, class size)."""
    G = [(A, mat_inv(A)) for A in gl3()]
    seen = set()
    reps = []
    for L in all_matrices():
        if L in seen:
            continue
        orbit = set()
        for A, Ai in G:
            M = mat_mul(mat_mul(A, L), Ai)
            for lam in range(3):
                orbit.add(tuple(tuple((M[i][j] + (lam if i == j else 0)) % 3 for j in range(3))
                                for i in range(3)))
        seen |= orbit
        reps.append((L, len(orbit)))
    return reps


def conjugate_map(P, A, Ai):
    """x -> A P(A^-1 x); has the same fibre sizes as P in every slice."""
    return [mat_vec(A, P[idx(mat_vec(Ai, x))]) for x in PTS]


def flat(L):
    return [L[i][j] for i in range(3) for j in range(3)]
