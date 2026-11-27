# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Exhaustive scans of field-structured maps P: F_27 -> F_27 for the block-length-3 entropy
question over F_3 (f27/F27.md).

For a map P: F_3^k -> F_3^k and X uniform on F_3^k, the score is

    S(P) = sum over t in F_3 of sum over v of c_t(v) log2 c_t(v),
    c_t(v) = #{x : P(x) + t x = v}.

h(P) = log2(3^k) - S(P) / (3 * 3^k) and h_k = min_P h(P).  The Kakeya growth base over F_3 is
beta_3 = inf_k 2^(h_k / k) (kakeya-small-fields, Theorem 2), and the coordinatewise product
of the best one-dimensional map has S = 162 at k = 3.  So a map with S(P) > 162 at k = 3
would give beta_3 < 3 / 2^(2/3) = 1.88988 (the bound of Kopparty, Lev, Saraf and Sudan).
Every quadratic map has S <= 162 (notes/a192.md, h3scan-v1).  This module scans families
that are NOT quadratic in general: F_27-polynomials with at most three terms, and linear
images of power maps, with or without an added F_3-linear map.

F_27 = F_3[a] / (a^3 + 2a + 1) (the Conway polynomial).  An element u0 + u1 a + u2 a^2 has
index u0 + 3 u1 + 9 u2, so addition of indices is vector addition in F_3^3, the setting of S.

Symmetries used (each preserves S; proofs in F27.md):
  * adding a constant to P;
  * conjugating P by an invertible F_3-linear map B: P -> B^-1 P B.  For B = multiplication
    by mu in F_27^*, the term c x^e becomes c mu^(e-1) x^e, so the first coefficient whose
    exponent is not 1 may be taken from a set of coset representatives (reps(e))."""
import itertools
import math
import os
import sys

_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if _ROOT not in sys.path:
    sys.path.insert(0, _ROOT)

N = 27
THRESH = 162
TWO162 = 2 ** 162


# ---------------------------------------------------------------- the field F_27

def to_vec(i):
    return (i % 3, (i // 3) % 3, i // 9)


def to_idx(v):
    return v[0] % 3 + 3 * (v[1] % 3) + 9 * (v[2] % 3)


def _pmul(u, v):
    r = [0] * 5
    for i in range(3):
        for j in range(3):
            r[i + j] += u[i] * v[j]
    # a^3 = a + 2 and a^4 = a^2 + 2a  (from a^3 + 2a + 1 = 0)
    r[2] += r[4]
    r[1] += 2 * r[4]
    r[1] += r[3]
    r[0] += 2 * r[3]
    return (r[0] % 3, r[1] % 3, r[2] % 3)


ADD = [[to_idx(tuple(a + b for a, b in zip(to_vec(i), to_vec(j)))) for j in range(N)]
       for i in range(N)]
MUL = [[to_idx(_pmul(to_vec(i), to_vec(j))) for j in range(N)] for i in range(N)]
ONE = 1


def power(x, e):
    r = ONE
    for _ in range(e):
        r = MUL[r][x]
    return r


# POW[e][x] = x^e for e >= 1 (0^e = 0); POW[0] is the constant 1.
POW = [[power(x, e) for x in range(N)] for e in range(N)]
# TX[t][x] = t x for t in F_3 (scalar multiple of the vector x).
TX = [[to_idx(tuple(t * c for c in to_vec(x))) for x in range(N)] for t in range(3)]
# COL[e][c][x] = c x^e
COL = [[[MUL[c][POW[e][x]] for x in range(N)] for c in range(N)] for e in range(N)]
CL = [0.0] + [c * math.log2(c) for c in range(1, N + 1)]


def order(x):
    if x == 0:
        return 0
    k, r = 1, x
    while r != ONE:
        r = MUL[r][x]
        k += 1
    return k


def primitive():
    for x in range(1, N):
        if order(x) == N - 1:
            return x
    return None


GEN = primitive()
UNITS = list(range(1, N))


# ---------------------------------------------------------------- the score

def counts(P):
    out = []
    for T in TX:
        cnt = [0] * N
        for p, tx in zip(P, T):
            cnt[ADD[p][tx]] += 1
        out.append(cnt)
    return out


def score(P):
    s = 0.0
    for T in TX:
        cnt = [0] * N
        for p, tx in zip(P, T):
            cnt[ADD[p][tx]] += 1
        s += sum([CL[c] for c in cnt])
    return s


def exact_q(P):
    """Q(P) = product over t and v of c^c, an integer with log2 Q = S(P)."""
    q = 1
    for cnt in counts(P):
        for c in cnt:
            if c > 1:
                q *= c ** c
    return q


def classify(P):
    """+1 if S(P) > 162, 0 if S(P) = 162, -1 if below (exact)."""
    q = exact_q(P)
    return (q > TWO162) - (q < TWO162)


def score_reference(P):
    """Independent implementation from coordinate tuples (no tables)."""
    from collections import Counter
    pts = [to_vec(x) for x in range(N)]
    s = 0.0
    for t in range(3):
        c = Counter(tuple((a + t * b) % 3 for a, b in zip(to_vec(P[x]), pts[x]))
                    for x in range(N))
        s += sum(v * math.log2(v) for v in c.values())
    return s


# ---------------------------------------------------------------- symmetry reduction

def reps(e):
    """Least index in each coset of the subgroup {mu^(e-1)} of F_27^*."""
    if e == 1:
        return list(UNITS)
    H = sorted(set(power(mu, e - 1) for mu in UNITS))
    return sorted(set(min(MUL[c][h] for h in H) for c in UNITS))


REPS = [None] + [reps(e) for e in range(1, N)]


def coef_choices(exps):
    """Coefficient lists for the terms x^e, e in exps (sorted, distinct, >= 1): the first
    exponent other than 1 gets REPS, every other term all of F_27^*."""
    out, done = [], False
    for e in exps:
        if not done and e != 1:
            out.append(REPS[e])
            done = True
        else:
            out.append(UNITS)
    return out


# ---------------------------------------------------------------- family 1: <= 3 terms

def poly_tasks():
    ex = range(1, N)
    tasks = [(e,) for e in ex]
    tasks += list(itertools.combinations(ex, 2))
    tasks += list(itertools.combinations(ex, 3))
    return tasks


def expected_poly_count():
    return sum(math.prod(len(c) for c in coef_choices(t)) for t in poly_tasks())


def _new_stat():
    return {"maps": 0, "max": -1.0, "arg": None, "beats": [], "ties": 0, "near": 0}


def _record(st, s, P, label):
    st["maps"] += 1
    if s > st["max"]:
        st["max"], st["arg"] = s, label
    if s > THRESH - 1e-6:
        st["near"] += 1
        k = classify(P)
        if k > 0 and len(st["beats"]) < 5:
            st["beats"].append((label, list(P)))
        elif k == 0:
            st["ties"] += 1


def poly_task(exps):
    st = _new_stat()
    ch = coef_choices(exps)
    if len(exps) == 1:
        (e,) = exps
        for c in ch[0]:
            P = COL[e][c]
            _record(st, score(P), P, (exps, (c,)))
        return st
    if len(exps) == 2:
        e1, e2 = exps
        for c1 in ch[0]:
            a = COL[e1][c1]
            for c2 in ch[1]:
                P = [ADD[u][v] for u, v in zip(a, COL[e2][c2])]
                _record(st, score(P), P, (exps, (c1, c2)))
        return st
    e1, e2, e3 = exps
    for c1 in ch[0]:
        a = COL[e1][c1]
        for c2 in ch[1]:
            b = [ADD[u][v] for u, v in zip(a, COL[e2][c2])]
            for c3 in ch[2]:
                P = [ADD[u][v] for u, v in zip(b, COL[e3][c3])]
                s = score(P)
                st["maps"] += 1
                if s > st["max"]:
                    st["max"], st["arg"] = s, (exps, (c1, c2, c3))
                if s > THRESH - 1e-6:
                    st["near"] += 1
                    k = classify(P)
                    if k > 0 and len(st["beats"]) < 5:
                        st["beats"].append(((exps, (c1, c2, c3)), list(P)))
                    elif k == 0:
                        st["ties"] += 1
    return st


# ---------------------------------------------------------------- family 2: power maps and linear maps

NONLIN = [e for e in range(2, N) if e not in (3, 9)]  # x, x^3, x^9 are F_3-linear


def linear_table(b0, b1, b2):
    """The F_3-linear map sending the basis vectors 1, a, a^2 (indices 1, 3, 9) to b0, b1, b2,
    as a table of its 27 values."""
    imgs = (b0, b1, b2)
    tab = []
    for x in range(N):
        v = to_vec(x)
        r = 0
        for coord, img in zip(v, imgs):
            for _ in range(coord):
                r = ADD[r][img]
        tab.append(r)
    return tab


def all_linear():
    for b0 in range(N):
        for b1 in range(N):
            for b2 in range(N):
                yield (b0, b1, b2), linear_table(b0, b1, b2)


def linear_task(b0):
    """For the 729 linear maps L with L(1) = b0: L itself, L o x^e, and c x^e + L
    (c in REPS[e]) for every non-linear exponent e."""
    st = {"lin": _new_stat(), "lpow": _new_stat(), "plus": _new_stat()}
    for b1 in range(N):
        for b2 in range(N):
            L = linear_table(b0, b1, b2)
            lab = (b0, b1, b2)
            _record(st["lin"], score(L), L, (lab,))
            for e in NONLIN:
                pe = POW[e]
                P = [L[y] for y in pe]
                _record(st["lpow"], score(P), P, (lab, e))
                for c in REPS[e]:
                    col = COL[e][c]
                    P = [ADD[u][v] for u, v in zip(col, L)]
                    _record(st["plus"], score(P), P, (lab, e, c))
    return st


def expected_linear_counts():
    nl = N ** 3
    return {"lin": nl, "lpow": nl * len(NONLIN),
            "plus": nl * sum(len(REPS[e]) for e in NONLIN)}


# ---------------------------------------------------------------- sweeps

def merge(stats):
    tot = _new_stat()
    for st in stats:
        tot["maps"] += st["maps"]
        tot["ties"] += st["ties"]
        tot["near"] += st["near"]
        if st["max"] > tot["max"]:
            tot["max"], tot["arg"] = st["max"], st["arg"]
        for b in st["beats"]:
            if len(tot["beats"]) < 5:
                tot["beats"].append(b)
    return tot


def run(fn, tasks, workers=8):
    if workers <= 1:
        return [fn(t) for t in tasks]
    import multiprocessing as mp
    pool = mp.get_context("spawn").Pool(workers)
    try:
        return list(pool.imap_unordered(fn, tasks, chunksize=4))
    finally:
        pool.close()
        pool.join()


def sweep_poly(workers=8):
    tasks = sorted(poly_tasks(), key=lambda t: -math.prod(len(c) for c in coef_choices(t)))
    return merge(run(poly_task, tasks, workers))


def sweep_linear(workers=8):
    res = run(linear_task, list(range(N)), workers)
    return {k: merge([r[k] for r in res]) for k in ("lin", "lpow", "plus")}


def describe(st):
    return ("maps=%d max=%.9f ties162=%d near=%d beats=%d arg=%r"
            % (st["maps"], st["max"], st["ties"], st["near"], len(st["beats"]), st["arg"]))
