# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""An exact SAT search for anisotropic systems (section 14 of finite-groups.md and
notes/rank-restriction.md): is there an anisotropic system with dim X = t and dim V = d?

Setting as in m6_sharp.py. X = F_2^t, V = F_2^d, sigma : V -> X quadratic with polar form beta,
alpha : V -> End(X) linear, A_h = alpha(h), and

    A_(h') sigma(h) = (I + A_h) beta(h, h')     for all h, h' in V.          (*)

Both sides are linear in h', so (*) holds for all h' iff it holds for h' = e_j, and then both sides
are polynomials of degree <= 2 in the coordinates of h. Comparing coefficients (h_i^2 = h_i), (*)
is equivalent to the vector equations

    A_j s_i = (I + A_i) B_ij                    for all i, j                    (L)
    A_j B_ik = A_i B_kj + A_k B_ij              for i < k and j not in {i, k}   (Q)

with A_i = alpha(e_i), s_i = sigma(e_i), B_ij = beta(e_i, e_j) and B_ii = 0. Anisotropy says
sigma(h) != 0 for each of the 2^d - 1 non-zero h. GL(X) acts on systems (A -> g A g^-1,
sigma -> g sigma, beta -> g beta), so we may assume the s_i are in echelon form: each s_i is either
e_r, where r is the rank of s_1, ..., s_(i-1), or lies in span(e_0, ..., e_(r-1)). The encoding is
plain CNF (Tseitin clauses for products and parities). A model is decoded and re-checked by brute
force on all pairs (h, h') with is_system, which does not use (L) or (Q). An UNSAT answer means
there is no anisotropic system with these (t, d), so A(t) < d.

Parts: selfcheck (pure Python: (L) and (Q) agree with brute force, and the CNF accepts exactly the
anisotropic systems, on known and random examples), solve (one instance, solved in a child process
with a time budget; needs python-sat), grade (the pre-registered predictions).

Vectors of F_2^m are int bitmasks; a t x t matrix is a t^2-bit mask with entry (r, c) at bit
t r + c (0-based). The helpers are copied from m6_sharp.py so that this file runs on its own.

Usage: python sat_aniso.py --part selfcheck|solve|grade [--t T --d D] [--nostar]
                           [--solver auto] [--budget-minutes 30] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time


def parity(x):
    return bin(x).count("1") & 1


def rank_f2(rows):
    """Rank of a list of int bitmasks over F_2."""
    pivots = {}
    r = 0
    for row in rows:
        x = row
        while x:
            hb = x.bit_length() - 1
            if hb in pivots:
                x ^= pivots[hb]
            else:
                pivots[hb] = x
                r += 1
                break
    return r


def independent(gens):
    """A maximal independent subset of gens, in order."""
    out = []
    for g in gens:
        if rank_f2(out + [g]) > len(out):
            out.append(g)
    return out


def nullspace(constraints, nbits):
    """Basis of {x in F_2^nbits : parity(c & x) = 0 for every c}, via reduced row echelon form."""
    pivots = []
    for c in constraints:
        x = c
        for col, r in pivots:
            if (x >> col) & 1:
                x ^= r
        if x:
            col = x.bit_length() - 1
            pivots = [(pc, r ^ x if (r >> col) & 1 else r) for pc, r in pivots] + [(col, x)]
    pcols = {col for col, _ in pivots}
    basis = []
    for f in range(nbits):
        if f in pcols:
            continue
        v = 1 << f
        for col, r in pivots:
            if (r >> f) & 1:
                v |= 1 << col
        basis.append(v)
    return basis


def combine(basis, c):
    """XOR of basis[t] over the set bits t of c."""
    out = 0
    t = 0
    while c:
        if c & 1:
            out ^= basis[t]
        c >>= 1
        t += 1
    return out


# ---------- t x t matrices over F_2 ----------

def mat_apply(A, x, t):
    row_mask = (1 << t) - 1
    out = 0
    for r in range(t):
        if parity((A >> (t * r)) & row_mask & x):
            out |= 1 << r
    return out


def entries(t, cells):
    """The matrix with a 1 in each (r, c) of cells (0-based)."""
    return sum(1 << (t * r + c) for r, c in cells)


def rows_of(A, t):
    row_mask = (1 << t) - 1
    return [(A >> (t * r)) & row_mask for r in range(t)]


def from_rows(rows, t):
    return sum(row << (t * r) for r, row in enumerate(rows))


def from_cols(cols, t):
    """The matrix whose column c is the vector cols[c]."""
    return from_rows([sum(((col >> r) & 1) << c for c, col in enumerate(cols))
                      for r in range(t)], t)


def mat_mul(A, B, t):
    rb = rows_of(B, t)
    out = []
    for row in rows_of(A, t):
        x = 0
        for c in range(t):
            if (row >> c) & 1:
                x ^= rb[c]
        out.append(x)
    return from_rows(out, t)


def mat_inv(A, t):
    """Inverse by Gauss-Jordan on [A | I]; ValueError if A is singular."""
    aug = [row | (1 << (t + r)) for r, row in enumerate(rows_of(A, t))]
    for col in range(t):
        p = next((r for r in range(col, t) if (aug[r] >> col) & 1), None)
        if p is None:
            raise ValueError("singular matrix")
        aug[col], aug[p] = aug[p], aug[col]
        for r in range(t):
            if r != col and (aug[r] >> col) & 1:
                aug[r] ^= aug[col]
    return from_rows([row >> t for row in aug], t)


# ---------- quadratic maps V -> F_2^t (from m6_sharp.py) ----------

def monomials(m):
    return [(i, i) for i in range(m)] + list(itertools.combinations(range(m), 2))


def mon_tables(m):
    return [sum(1 << h for h in range(1 << m) if (h >> i) & 1 and (h >> j) & 1)
            for i, j in monomials(m)]


def sigma_from_coeffs(c, tabs, t):
    """sigma for the coefficient vector c, as t masks over h (bit h of mask i = coordinate i)."""
    N = len(tabs)
    return tuple(combine(tabs, (c >> (i * N)) & ((1 << N) - 1)) for i in range(t))


def sig(S, h):
    out = 0
    for i, q in enumerate(S):
        out |= ((q >> h) & 1) << i
    return out


def table(S, m):
    """Value table [sigma(h) for h in V] of the masks S."""
    return [sig(S, h) for h in range(1 << m)]


def system(Cbasis, y):
    """(m, alpha table) for V = F_2^(c + y), alpha = basis combination of the first c coordinates."""
    c = len(Cbasis)
    m = c + y
    cmask = (1 << c) - 1
    return m, [combine(Cbasis, h & cmask) for h in range(1 << m)]


def solve_sigma(at, m, t):
    """Basis (coefficient vectors) of every sigma satisfying (*) for the alpha table at."""
    mons = monomials(m)
    N = len(mons)
    w2 = [0] + [1 << i for i in range(m)] + [(1 << i) | (1 << j)
                                            for i, j in itertools.combinations(range(m), 2)]
    pairs = [(h, 1 << i) for h in w2 for i in range(m)]
    rows = [0] * (t * len(pairs))
    for u in range(t * N):
        comp, k = divmod(u, N)
        i, j = mons[k]
        bit = 1 << u
        for p, (h, hp) in enumerate(pairs):
            s = (((h >> i) & 1) & ((h >> j) & 1)) << comp
            pol = 0 if i == j else ((((h >> i) & 1) & ((hp >> j) & 1))
                                    ^ (((h >> j) & 1) & ((hp >> i) & 1)))
            if not s and not pol:
                continue
            bb = pol << comp
            e = mat_apply(at[hp], s, t) ^ bb ^ mat_apply(at[h], bb, t)
            r = 0
            while e:
                if e & 1:
                    rows[t * p + r] |= bit
                e >>= 1
                r += 1
    return nullspace(rows, t * N)


def is_system(at, sv, m, t):
    """Does (*) hold for the alpha table at and the value table sv on F_2^m?"""
    for h in range(1 << m):
        s = sv[h]
        for hp in range(1 << m):
            b = sv[h ^ hp] ^ s ^ sv[hp]
            if mat_apply(at[hp], s, t) != b ^ mat_apply(at[h], b, t):
                return False
    return True


def anisotropic(sv):
    return all(sv[h] for h in range(1, len(sv)))


def restrict(at, sv, basis):
    """(k, alpha table, value table) of the system restricted to span(basis), in its coordinates."""
    vals = [combine(basis, c) for c in range(1 << len(basis))]
    return len(basis), [at[v] for v in vals], [sv[v] for v in vals]


def greedy_anisotropic(sv, m, rng):
    """Basis of a maximal subspace of F_2^m on which sigma has no non-zero zero (random order)."""
    order = list(range(1, 1 << m))
    rng.shuffle(order)
    basis, span, seen = [], [0], {0}
    for v in order:
        if v in seen or not sv[v]:
            continue
        new = [v ^ w for w in span]
        if all(sv[x] for x in new):
            basis.append(v)
            span += new
            seen.update(new)
    return basis


def diagonal(t):
    """Lemma 23(d): V = F_2^(2t) with u in bits 0..t-1 and v in bits t..2t-1, A_h = diag(u),
    sigma_i = (1 + u_i) v_i."""
    at, sv = [], []
    for h in range(1 << (2 * t)):
        u, v = h & ((1 << t) - 1), h >> t
        at.append(sum(1 << (t * i + i) for i in range(t) if (u >> i) & 1))
        sv.append(~u & v & ((1 << t) - 1))
    return 2 * t, at, sv


# ---------- systems by coordinates (A_i, s_i, B_ik) ----------

def extract(at, sv, d):
    """(A list, s list, B dict) of a linear alpha table and a quadratic value table on F_2^d."""
    As = [at[1 << i] for i in range(d)]
    ss = [sv[1 << i] for i in range(d)]
    B = {(i, k): sv[(1 << i) | (1 << k)] ^ ss[i] ^ ss[k]
         for i, k in itertools.combinations(range(d), 2)}
    return As, ss, B


def tables(As, ss, B, d):
    """(alpha table, value table) on F_2^d of the coordinates (A_i, s_i, B_ik)."""
    at, sv = [], []
    for h in range(1 << d):
        idx = [i for i in range(d) if (h >> i) & 1]
        a = s = 0
        for i in idx:
            a ^= As[i]
            s ^= ss[i]
        for i, k in itertools.combinations(idx, 2):
            s ^= B[(i, k)]
        at.append(a)
        sv.append(s)
    return at, sv


def coeff_ok(As, ss, B, t, d):
    """The equations (L) and (Q)."""
    def bv(i, k):
        return 0 if i == k else B[(min(i, k), max(i, k))]
    for i in range(d):
        for j in range(d):
            b = bv(i, j)
            if mat_apply(As[j], ss[i], t) != b ^ mat_apply(As[i], b, t):
                return False
    for i, k in itertools.combinations(range(d), 2):
        for j in range(d):
            if j in (i, k):
                continue
            if mat_apply(As[j], bv(i, k), t) != (mat_apply(As[i], bv(k, j), t)
                                                ^ mat_apply(As[k], bv(i, j), t)):
                return False
    return True


def in_echelon(ss, t):
    r = 0
    for s in ss:
        if r < t and s == 1 << r:
            r += 1
        elif s >> r:
            return False
    return True


def normalize(As, ss, B, t):
    """g (As, ss, B) for a g in GL(X) that puts the s_i in echelon form."""
    piv = independent(ss)
    cols = list(piv)
    for f in range(t):
        if rank_f2(cols + [1 << f]) > len(cols):
            cols.append(1 << f)
    Q = from_cols(cols, t)
    g = mat_inv(Q, t)
    return ([mat_mul(mat_mul(g, A, t), Q, t) for A in As], [mat_apply(g, s, t) for s in ss],
            {k: mat_apply(g, v, t) for k, v in B.items()})


# ---------- CNF encoding ----------

class CNF:
    def __init__(self):
        self.nv = 0
        self.clauses = []
        self.defs = {}          # auxiliary var -> ("and", x, y) or ("xor", [vars])
        self.ands = {}

    def new(self):
        self.nv += 1
        return self.nv

    def AND(self, x, y):
        key = (min(x, y), max(x, y))
        if key not in self.ands:
            p = self.new()
            self.clauses += [[-p, x], [-p, y], [p, -x, -y]]
            self.defs[p] = ("and", x, y)
            self.ands[key] = p
        return self.ands[key]

    def parity_clauses(self, vs, rhs):
        """Forbid every assignment of the variables vs whose parity is not rhs."""
        for bits in range(1 << len(vs)):
            if parity(bits) != rhs:
                self.clauses.append([-v if (bits >> i) & 1 else v for i, v in enumerate(vs)])

    def xor_eq(self, lits, rhs):
        """The sum of the literals is rhs over F_2."""
        count = {}
        for lit in lits:
            if lit < 0:
                rhs ^= 1
                lit = -lit
            count[lit] = count.get(lit, 0) ^ 1
        vs = [v for v, c in count.items() if c]
        while len(vs) > 4:
            z = self.new()
            self.defs[z] = ("xor", vs[:3])
            self.parity_clauses(vs[:3] + [z], 0)
            vs = [z] + vs[3:]
        if vs:
            self.parity_clauses(vs, rhs)
        elif rhs:
            self.clauses.append([])

    def xor_def(self, vs):
        """A new variable equal to the sum of the (positive) variables vs."""
        z = self.new()
        self.defs[z] = ("xor", list(vs))
        self.xor_eq(list(vs) + [z], 0)
        return z


def encode(t, d, star=True, aniso=True, echelon=True):
    """CNF whose models are the anisotropic systems (t, d) with s_i in echelon form (each part can
    be switched off). Returns (cnf, (A, S, B, R, N)) with A[i][r][c], S[i][r], B[(i, k)][r]."""
    cnf = CNF()
    A = [[[cnf.new() for c in range(t)] for r in range(t)] for i in range(d)]
    S = [[cnf.new() for r in range(t)] for i in range(d)]
    B = {(i, k): [cnf.new() for r in range(t)] for i, k in itertools.combinations(range(d), 2)}

    def bv(i, k):
        return None if i == k else B[(min(i, k), max(i, k))]

    def prods(M, vec, r):
        return [cnf.AND(M[r][c], vec[c]) for c in range(t)]

    if star:
        for i in range(d):
            for j in range(d):
                b = bv(i, j)
                for r in range(t):
                    lits = prods(A[j], S[i], r)
                    if b is not None:
                        lits += [b[r]] + prods(A[i], b, r)
                    cnf.xor_eq(lits, 0)
        for i, k in itertools.combinations(range(d), 2):
            for j in range(d):
                if j in (i, k):
                    continue
                for r in range(t):
                    cnf.xor_eq(prods(A[j], bv(i, k), r) + prods(A[i], bv(k, j), r)
                               + prods(A[k], bv(i, j), r), 0)
    if aniso:
        Y = {}
        for h in range(1, 1 << d):
            k = h.bit_length() - 1
            hp = h ^ (1 << k)
            ys = []
            for r in range(t):
                vs = [S[k][r]] + [B[(i, k)][r] for i in range(k) if (hp >> i) & 1]
                if hp:
                    vs.append(Y[hp][r])
                ys.append(cnf.xor_def(vs))
            Y[h] = ys
            cnf.clauses.append(list(ys))
    R, N = None, None
    if echelon:
        R = [[cnf.new() for r in range(t + 1)] for i in range(d + 1)]
        N = [None] + [cnf.new() for i in range(d)]
        cnf.clauses.append([R[0][0]])
        cnf.clauses += [[-R[0][r]] for r in range(1, t + 1)]
        for i in range(1, d + 1):
            cnf.clauses.append(list(R[i]))
            cnf.clauses += [[-R[i][a], -R[i][b]] for a, b in itertools.combinations(range(t + 1), 2)]
            s, n = S[i - 1], N[i]
            for r in range(t + 1):
                p = R[i - 1][r]
                if r == t:
                    cnf.clauses.append([-p, -n])
                else:
                    cnf.clauses += [[-p, -n, s[c]] if c == r else [-p, -n, -s[c]]
                                    for c in range(t)]
                    cnf.clauses.append([-p, -n, R[i][r + 1]])
                cnf.clauses += [[-p, n, -s[c]] for c in range(r, t)]
                cnf.clauses.append([-p, n, R[i][r]])
    return cnf, (A, S, B, R, N)


def assignment(cnf, names, As, ss, B, t, d):
    """The full assignment that the system (As, ss, B) induces on every variable of encode()."""
    A, S, Bv, R, N = names
    val = {}
    for i in range(d):
        for r in range(t):
            val[S[i][r]] = bool((ss[i] >> r) & 1)
            for c in range(t):
                val[A[i][r][c]] = bool((As[i] >> (t * r + c)) & 1)
    for key, vs in Bv.items():
        for r in range(t):
            val[vs[r]] = bool((B[key] >> r) & 1)
    if R is not None:
        rank = 0
        for i in range(d + 1):
            if i:
                new = rank < t and ss[i - 1] == 1 << rank
                val[N[i]] = new
                rank += new
            for r in range(t + 1):
                val[R[i][r]] = r == rank
    for v in sorted(cnf.defs):
        kind = cnf.defs[v]
        if kind[0] == "and":
            val[v] = val[kind[1]] and val[kind[2]]
        else:
            val[v] = sum(val[x] for x in kind[1]) % 2 == 1
    return val


def satisfies(cnf, val):
    return all(any(val[lit] if lit > 0 else not val[-lit] for lit in cl) for cl in cnf.clauses)


def cnf_accepts(As, ss, B, t, d, **kw):
    cnf, names = encode(t, d, **kw)
    return satisfies(cnf, assignment(cnf, names, As, ss, B, t, d))


def decode(model, names, t, d):
    A, S, Bv, R, N = names
    pos = {lit for lit in model if lit > 0}
    As = [sum(1 << (t * r + c) for r in range(t) for c in range(t) if A[i][r][c] in pos)
          for i in range(d)]
    ss = [sum(1 << r for r in range(t) if S[i][r] in pos) for i in range(d)]
    B = {key: sum(1 << r for r in range(t) if vs[r] in pos) for key, vs in Bv.items()}
    return As, ss, B


# ---------- known examples ----------

def example1():
    """Example 1 of finite-groups.md (t = 3, d = 2): A_1 = E_11, A_2 = E_12 + E_13 + E_21 + E_22,
    sigma(e_1) = e_2 + e_3, sigma(e_2) = e_1 + e_2 + e_3, beta(e_1, e_2) = e_2 (1-based)."""
    t = 3
    return ([entries(t, [(0, 0)]), entries(t, [(0, 1), (0, 2), (1, 0), (1, 1)])], [6, 7],
            {(0, 1): 2})


def norm_pair():
    """sigma(x, y, z, w) = (x + y + xy, z + w + zw) on F_2^4 -> F_2^2 (two copies of the norm form
    of F_4): anisotropic, already in echelon form, and not a system with alpha = 0."""
    return [0, 0, 0, 0], [1, 1, 2, 2], {(0, 1): 1, (2, 3): 2, (0, 2): 0, (0, 3): 0, (1, 2): 0,
                                        (1, 3): 0}


def random_examples(rng, count):
    """(t, d, As, ss, B) from random solutions of (*), their anisotropic restrictions, the diagonal
    system, and one-bit mutations of each."""
    out = []
    while len(out) < count:
        t = rng.choice((2, 3))
        if rng.random() < 0.25:
            m, at, sv = diagonal(t)
        else:
            mats = independent([rng.getrandbits(t * t) for _ in range(rng.randint(1, 3))])
            m, at = system(mats, rng.randint(0, 1))
            sol = solve_sigma(at, m, t)
            if not sol:
                continue
            sv = table(sigma_from_coeffs(combine(sol, rng.getrandbits(len(sol))), mon_tables(m), t),
                       m)
        basis = greedy_anisotropic(sv, m, rng) if rng.random() < 0.7 else list(
            1 << i for i in range(min(m, 4)))
        if not basis:
            continue
        d, at_w, sv_w = restrict(at, sv, basis)
        As, ss, B = extract(at_w, sv_w, d)
        out.append((t, d, As, ss, B))
        As2, ss2, B2 = list(As), list(ss), dict(B)
        which = rng.randrange(3 if B else 2)
        if which == 0:
            i = rng.randrange(d)
            As2[i] ^= 1 << rng.randrange(t * t)
        elif which == 1:
            i = rng.randrange(d)
            ss2[i] ^= 1 << rng.randrange(t)
        else:
            key = rng.choice(sorted(B2))
            B2[key] ^= 1 << rng.randrange(t)
        out.append((t, d, As2, ss2, B2))
    return out


def selfcheck(rng, count=160):
    st = {"cases": 0, "systems": 0, "aniso_systems": 0, "coeff_disagree": 0, "cnf_disagree": 0,
          "echelon_disagree": 0}
    for t, d, As, ss, B in random_examples(rng, count):
        at, sv = tables(As, ss, B, d)
        sysok = is_system(at, sv, d, t)
        good = sysok and anisotropic(sv)
        st["cases"] += 1
        st["systems"] += sysok
        st["aniso_systems"] += good
        st["coeff_disagree"] += coeff_ok(As, ss, B, t, d) != sysok
        st["cnf_disagree"] += cnf_accepts(As, ss, B, t, d, echelon=False) != good
        nAs, nss, nB = normalize(As, ss, B, t)
        st["echelon_disagree"] += cnf_accepts(nAs, nss, nB, t, d) != good
    st["graded"] = {"coeff_agree": st["coeff_disagree"] == 0, "cnf_agree": st["cnf_disagree"] == 0,
                    "echelon_agree": st["echelon_disagree"] == 0,
                    "nontrivial": 0 < st["aniso_systems"] < st["cases"]}
    return st


# ---------- solving ----------

SOLVERS = ("cadical195", "cadical153", "glucose4")


def child(t, d, star, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode(t, d, star=star)
    start = time.time()
    names_to_try = SOLVERS if solver == "auto" else (solver,)
    used = None
    for name in names_to_try:
        try:
            s = Solver(name=name, bootstrap_with=cnf.clauses)
            used = name
            break
        except Exception:
            continue
    if used is None:
        raise RuntimeError("no SAT solver available")
    ok = s.solve()
    res = {"status": "SAT" if ok else "UNSAT", "solver": used, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = decode(s.get_model(), names, t, d)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def instance_name(t, d, star, solver):
    return f"t{t}_d{d}" + ("" if star else "_nostar") + ("" if solver == "auto" else "_" + solver)


def solve(t, d, star, solver, budget_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    name = instance_name(t, d, star, solver)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--d",
           str(d), "--solver", solver, "--child-out", path] + ([] if star else ["--nostar"])
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "d": d, "star": star, "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, k): v for i, k, v in res["B"]}
        at, sv = tables(As, ss, B, d)
        res["verified_system"] = is_system(at, sv, d, t)
        res["verified_anisotropic"] = anisotropic(sv)
        res["verified_echelon"] = in_echelon(ss, t)
        res["ranks"] = sorted(rank_f2(rows_of(at[h], t)) for h in range(1, 1 << d))
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


# Pre-registered (notes/predictions.md of run 56). SAT answers count only with a model that passes
# the brute-force checks; UNKNOWN (time budget reached) is reported and not graded.
EXPECTED = {"t1_d1": "SAT", "t2_d2": "SAT", "t3_d3": "SAT", "t4_d4": "SAT", "t5_d5": "SAT",
            "t1_d2": "UNSAT", "t2_d3": "UNSAT", "t3_d4": "UNSAT", "t2_d4": "UNSAT",
            "t2_d4_nostar": "SAT", "t4_d5": "UNSAT", "t3_d4_glucose4": "UNSAT",
            "t4_d5_glucose4": "UNSAT"}
EXPLORATORY = ("t5_d6", "t6_d7", "t5_d6_glucose4")


def grade(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.endswith(".json") and not fn.endswith(".child.json") and fn.startswith("t"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    graded, ungraded = {}, {}
    for name, want in EXPECTED.items():
        r = results.get(name)
        if r is None or r["status"] in ("UNKNOWN", "ERROR"):
            ungraded[name] = "missing" if r is None else r["status"]
            continue
        ok = r["status"] == want
        if r["status"] == "SAT":
            ok = (ok and (r["verified_system"] or not r["star"]) and r["verified_anisotropic"]
                  and r["verified_echelon"])
        graded[name] = ok
    explore = {name: {k: results[name].get(k) for k in ("status", "seconds", "verified_system",
                                                         "verified_anisotropic", "ranks")}
               for name in EXPLORATORY if name in results}
    return {"graded": graded, "ungraded": ungraded, "exploratory": explore,
            "times": {n: r.get("wall_seconds") for n, r in results.items()}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--d", type=int, default=4)
    ap.add_argument("--nostar", action="store_true")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=30.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.d, not args.nostar, args.solver, args.child_out)
    elif args.part == "solve":
        res = solve(args.t, args.d, not args.nostar, args.solver, args.budget_minutes * 60,
                    args.out_dir)
        print(f"SUMMARY {res['name']} {res['status']}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {sorted(out['ungraded'])}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck(random.Random(31))
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
