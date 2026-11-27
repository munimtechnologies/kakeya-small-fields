# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Characteristic-3 entropy linear programs for the Kakeya constant over F_3 (f3cert/PREREG.md).

Setting.  A vertex is a pair (x, y) of F_3^n-valued random variables whose difference
d = x - y determines (x, y) ("difference-injective").  In
characteristic 3 the four forms x, y, s = x + y, d = x - y are the four points of P^1(F_3), and a
Kakeya set K of F_3^n gives such a pair with x, y, -s in K and d uniform on the non-zero
vectors.  Any linear-programming certificate of

    h(x) = h(y) = h(s) = w * h(d)   (symmetric after the rotation trick, see PREREG.md)

being impossible below w gives |K| >= (3^n - 1)^(w - o(1)), i.e. beta_3 >= 3^w.  For comparison:
Katz-Tao's 11/6 gives w = 6/11 (base 1.82074), Farnamfar's record C = 1.8263483657 (arXiv
2611.19594, valid in every abelian group without 2-torsion) gives base 1.82492, and the
Kopparty-Lev-Saraf-Sudan construction shows w <= 1 - (2/3)/log2(3) = 0.579380 (base 1.88988),
so no sound LP may exceed that value.

Model.  Farnamfar's certificates stack conditional copies of vertex pairs z_v = (x_v, y_v).  We
rebuild every configuration as F_3-LINEAR forms in "symbols": vertex 0 is (e0, e1); copying the
vertices U over glue readings V adds one new symbol per vector of a complement of span(V) in
span(U).  The entropy of a set of forms is the entropy of their F_3-span, closed under the
difference-injectivity rule (d_v in T => x_v, y_v in T).  Equal-law identifications of copies
are found on demand.  Characteristic 3 enters three ways that a general abelian group lacks:
  1. spans are taken over F_3 (e.g. x0 + 2 y1 = x0 - y1), so more entropy classes coincide;
  2. submodularity may use the intersection of the two closed spans (I(A;B) >= H(A cap B));
  3. "uniform" bounds: h(T) <= dim_F3(T) * h(d), since every form takes values in F_3^n and d is
     (asymptotically) uniform on F_3^n.  Kakeya-specific; false for general sum-difference sets.

Vectors over F_3 are bit-sliced pairs (p, n) of Python ints: bit c of p (of n) is set when
coordinate c equals 1 (equals 2)."""
import argparse
import hashlib
import json
import math
import os
import random
import sys
import time
import urllib.request
from fractions import Fraction

# ------------------------------------------------------------------ F_3 vectors (bit-sliced)

ZERO = (0, 0)


def vadd(x, y):
    xp, xn = x
    yp, yn = y
    x0 = ~(xp | xn)
    y0 = ~(yp | yn)
    return ((x0 & yp) | (xp & y0) | (xn & yn),
            (x0 & yn) | (xn & y0) | (xp & yp))


def vneg(x):
    return (x[1], x[0])


def vsub(x, y):
    return vadd(x, (y[1], y[0]))


def vscale(c, x):
    c %= 3
    if c == 0:
        return ZERO
    if c == 1:
        return x
    return (x[1], x[0])


def vsupp(x):
    return x[0] | x[1]


def coef(x, c):
    if (x[0] >> c) & 1:
        return 1
    if (x[1] >> c) & 1:
        return 2
    return 0


def unit(k):
    return (1 << k, 0)


def to_list(x, m):
    return [coef(x, c) for c in range(m)]


def from_list(lst):
    p = n = 0
    for c, a in enumerate(lst):
        a %= 3
        if a == 1:
            p |= 1 << c
        elif a == 2:
            n |= 1 << c
    return (p, n)


def to_digits(x, m):
    return "".join(str(coef(x, c)) for c in range(m))


# ------------------------------------------------------------------ subspaces of F_3^m

class Span:
    """A subspace in fully reduced row echelon form (pivot = highest set coordinate, pivot
    coefficient 1).  With track=True every row carries an image vector, so that a linear map
    defined on a basis can be applied to any vector of the span (reduce() returns it)."""
    __slots__ = ("rows", "img", "supp")

    def __init__(self, track=False):
        self.rows = {}
        self.img = {} if track else None
        self.supp = 0

    def copy(self, track=None):
        if track is None:
            track = self.img is not None
        s = Span(track)
        s.rows = dict(self.rows)
        if track:
            s.img = dict(self.img)
        s.supp = self.supp
        return s

    def dim(self):
        return len(self.rows)

    def reduce(self, v):
        """Return (r, acc) with v = r + sum_c alpha_c rows[c], r zero at every pivot, and
        acc = sum_c alpha_c img[c] (ZERO when untracked)."""
        acc = ZERO
        if not (vsupp(v) & self.supp):
            return v, acc
        tr = self.img is not None
        for c, r in self.rows.items():
            if (v[0] >> c) & 1:          # coefficient 1
                v = vsub(v, r)
                if tr:
                    acc = vadd(acc, self.img[c])
            elif (v[1] >> c) & 1:        # coefficient 2: v = 2 r + (v + r)
                v = vadd(v, r)
                if tr:
                    acc = vsub(acc, self.img[c])
        return v, acc

    def contains(self, v):
        if vsupp(v) & ~self.supp:
            return False
        return self.reduce(v)[0] == ZERO

    def insert(self, v, im=None):
        r, acc = self.reduce(v)
        if r == ZERO:
            return False
        tr = self.img is not None
        if tr:
            im = vsub(im if im is not None else ZERO, acc)
        c = vsupp(r).bit_length() - 1
        if (r[1] >> c) & 1:
            r = vneg(r)
            if tr:
                im = vneg(im)
        for c2 in list(self.rows):
            row = self.rows[c2]
            if (row[0] >> c) & 1:
                self.rows[c2] = vsub(row, r)
                if tr:
                    self.img[c2] = vsub(self.img[c2], im)
            elif (row[1] >> c) & 1:
                self.rows[c2] = vadd(row, r)
                if tr:
                    self.img[c2] = vadd(self.img[c2], im)
        self.rows[c] = r
        if tr:
            self.img[c] = im
        s = 0
        for row in self.rows.values():
            s |= row[0] | row[1]
        self.supp = s
        return True

    def key(self, kw):
        k = len(self.rows)
        for c in sorted(self.rows):
            p, n = self.rows[c]
            k = (((k << kw) | p) << kw) | n
        return k

    def basis(self):
        return [self.rows[c] for c in sorted(self.rows)]


def span_of(vecs):
    s = Span()
    for v in vecs:
        s.insert(v)
    return s


def intersect(A, B, m):
    """A cap B by the Zassenhaus algorithm (vectors (a, a) and (b, 0), left half on top)."""
    Z = Span()
    for r in A.rows.values():
        Z.insert(((r[0] << m) | r[0], (r[1] << m) | r[1]))
    for r in B.rows.values():
        Z.insert((r[0] << m, r[1] << m))
    out = Span()
    mask = (1 << m) - 1
    for c, r in Z.rows.items():
        if c < m:
            out.insert((r[0] & mask, r[1] & mask))
    return out


# ------------------------------------------------------------------ stacked configurations

class Config:
    """Vertices z_v = (X[v], Y[v]) as F_3-linear forms in symbols e_0, e_1, ...  Vertex 0 is
    (e_0, e_1).  add_step(U, V) is a conditional copy of the vertices U over the readings V
    (each a (vertex, (a, b)) pair meaning a x_v + b y_v with v in U); new vertices are
    numbered consecutively in the order of U."""

    def __init__(self):
        self.X = [unit(0)]
        self.Y = [unit(1)]
        self.nsym = 2
        self.steps = []
        self.Dv = None

    def nv(self):
        return len(self.X)

    def form(self, v, a, b):
        return vadd(vscale(a, self.X[v]), vscale(b, self.Y[v]))

    def D(self, v):
        return vsub(self.X[v], self.Y[v])

    def S(self, v):
        return vadd(self.X[v], self.Y[v])

    def readings(self, v):
        return [self.X[v], self.Y[v], self.S(v), self.D(v)]

    def add_step(self, U, V):
        old = self.nsym
        Uset = set(U)
        G = Span(track=True)
        for (v, (a, b)) in V:
            if v not in Uset:
                raise ValueError("glue reading outside U")
            f = self.form(v, a, b)
            G.insert(f, f)
        W = G.copy()
        comp = []
        for u in U:
            for f in (self.X[u], self.Y[u]):
                if not W.contains(f):
                    k = self.nsym
                    self.nsym += 1
                    W.insert(f, unit(k))
                    comp.append((k, f))

        def phi(f):
            r, acc = W.reduce(f)
            if r != ZERO:
                raise ValueError("form outside span(U)")
            return acc

        Inv = Span(track=True)
        for g in G.rows.values():
            Inv.insert(g, g)
        for k, f in comp:
            Inv.insert(unit(k), f)
        newv = []
        for u in U:
            self.X.append(phi(self.X[u]))
            self.Y.append(phi(self.Y[u]))
            newv.append(len(self.X) - 1)
        Gp = G.copy(track=False)
        st = {"U": list(U), "V": list(V), "new": newv, "old": old, "nnew": len(comp),
              "newmask": ((1 << self.nsym) - 1) ^ ((1 << old) - 1),
              "G": Gp, "Inv": Inv, "W": W, "comp": comp, "phi": phi}
        self.steps.append(st)
        self.Dv = None
        return st

    def finish(self):
        self.Dv = [self.D(v) for v in range(self.nv())]
        self.Dsupp = [vsupp(d) for d in self.Dv]
        return self


def build_config(steps):
    cfg = Config()
    for st in steps:
        U = [int(u) for u in st["U"]]
        V = [(int(f[0]), (int(f[1][0]), int(f[1][1]))) for f in st["V"]]
        cfg.add_step(U, V)
    return cfg.finish()


TOMAR_PAGE = [  # Tomar's initial six-pair page (z0..z5), as quoted in arXiv 2611.19594 sec. 3
    {"U": [0], "V": [[0, [1, 0]]]},
    {"U": [0, 1], "V": [[0, [0, 1]], [1, [0, 1]]]},
    {"U": [0, 1], "V": [[0, [1, 1]], [1, [0, 1]]]},
]


def closure(cfg, T):
    C = T.copy(track=False)
    X, Dv, Ds = cfg.X, cfg.Dv, cfg.Dsupp
    changed = True
    while changed:
        changed = False
        for v in range(len(X)):
            if Ds[v] & ~C.supp:
                continue
            if C.contains(Dv[v]) and not C.contains(X[v]):
                C.insert(X[v])
                changed = True
    return C


def preimage(st, T):
    Inv = st["Inv"]
    if T.supp & ~Inv.supp:
        return None
    out = Span()
    for r in T.rows.values():
        rem, acc = Inv.reduce(r)
        if rem != ZERO:
            return None
        out.insert(acc)
    return out


class Registry:
    """Entropy classes: closed F_3-spans, merged by a union-find whenever two classes have
    equal entropy by an equal-law identification of a conditional copy.  ub[root] is the
    smallest F_3-dimension of a raw span generating the class (the 'uniform' bound)."""

    def __init__(self, cfg, trace=None):
        self.cfg = cfg
        self.kw = cfg.nsym + 1
        self.ids = {}
        self.parent = []
        self.ub = []
        self.ubspan = []
        self.rawdone = set()
        self.trace = trace

    def find(self, a):
        p = self.parent
        while p[a] != a:
            p[a] = p[p[a]]
            a = p[a]
        return a

    def union(self, a, b):
        ra, rb = self.find(a), self.find(b)
        if ra == rb:
            return ra
        if rb < ra:
            ra, rb = rb, ra
        self.parent[rb] = ra
        if self.ub[rb] < self.ub[ra]:
            self.ub[ra] = self.ub[rb]
            self.ubspan[ra] = self.ubspan[rb]
        return ra

    def cls_c(self, T):
        rd = T.dim()
        C = closure(self.cfg, T)
        ck = C.key(self.kw)
        cid = self.ids.get(ck)
        if cid is None:
            cid = len(self.parent)
            self.ids[ck] = cid
            self.parent.append(cid)
            self.ub.append(C.dim())
            self.ubspan.append(tuple(C.basis()))
            if self.trace:
                self.trace(C, cid)
            self._eqlaw(C, cid)
        r = self.find(cid)
        if rd < self.ub[r]:
            self.ub[r] = rd
            self.ubspan[r] = tuple(T.basis())
        rk = T.key(self.kw)
        if rk != ck and rk not in self.rawdone:
            self.rawdone.add(rk)
            if self.trace:
                self.trace(T, cid)
            self._eqlaw(T, cid)
        return self.find(cid), C

    def cls(self, T):
        return self.cls_c(T)[0]

    def _eqlaw(self, T, cid):
        for st in self.cfg.steps:
            if not (T.supp & st["newmask"]):
                continue
            P = preimage(st, T)
            if P is None:
                continue
            pid = self.cls(P)
            self.union(cid, pid)


# ------------------------------------------------------------------ rows

def parse_form(cfg, f):
    return cfg.form(int(f[0]), int(f[1][0]), int(f[1][1]))


def sub_row(reg, Kvecs, i, j, meet):
    """h(K+i) + h(K+j) - h(K+i+j) - h(M) >= 0 with M = K (plain) or M = cl(K+i) cap cl(K+j).
    Returns (terms, spec) or (None, None) when the row is trivially 0."""
    K = span_of(Kvecs)
    A = K.copy()
    A.insert(i)
    B = K.copy()
    B.insert(j)
    AB = A.copy()
    AB.insert(j)
    a, Ac = reg.cls_c(A)
    b, Bc = reg.cls_c(B)
    ab = reg.cls(AB)
    if meet:
        mm = reg.cls(intersect(Ac, Bc, reg.cfg.nsym))
    else:
        mm = reg.cls(K)
    terms = [(a, 1), (b, 1), (ab, -1), (mm, -1)]
    return terms, ("sub" if not meet else "meet", tuple(Kvecs), i, j)


def mono_rows(reg, Kvecs, i, j):
    K = span_of(Kvecs)
    A = K.copy()
    A.insert(i)
    B = K.copy()
    B.insert(j)
    AB = A.copy()
    AB.insert(j)
    a, b, ab, k = reg.cls(A), reg.cls(B), reg.cls(AB), reg.cls(K)
    out = []
    for lo, hi, spec in ((a, ab, (Kvecs, i, j, "A<AB")), (b, ab, (Kvecs, i, j, "B<AB")),
                         (k, a, (Kvecs, i, j, "K<A"))):
        out.append(([(hi, 1), (lo, -1)], ("mono",) + tuple(spec)))
    return out


def ci_spans(cfg, st):
    O = Span()
    for k in range(st["old"]):
        O.insert(unit(k))
    OU = O.copy()
    for k in range(st["old"], st["old"] + st["nnew"]):
        OU.insert(unit(k))
    Up = st["Inv"].copy(track=False)
    return Up, O, OU, st["G"]


def ci_row(reg, s):
    """Farnamfar's ci row h(V,U') + h(O) - h(O,U') - h(V) = 0 for copy step s."""
    Up, O, OU, G = ci_spans(reg.cfg, reg.cfg.steps[s])
    terms = [(reg.cls(Up), 1), (reg.cls(O), 1), (reg.cls(OU), -1), (reg.cls(G), -1)]
    return terms, ("ci", s)


def apply_eqlaw(reg, cert):
    """Explicit equal-law generators of a certificate: h(T) = h(phi_s(T))."""
    done = skipped = 0
    for e in cert.get("eqlaw", []):
        st = reg.cfg.steps[int(e["step"])]
        try:
            T = span_of([parse_form(reg.cfg, f) for f in e["gens"]])
            Tp = span_of([st["phi"](parse_form(reg.cfg, f)) for f in e["gens"]])
        except ValueError:
            skipped += 1
            continue
        reg.union(reg.cls(T), reg.cls(Tp))
        done += 1
    return done, skipped


def vertex0(reg):
    cfg = reg.cfg
    x = reg.cls(span_of([cfg.X[0]]))
    y = reg.cls(span_of([cfg.Y[0]]))
    s = reg.cls(span_of([cfg.S(0)]))
    d = reg.cls(span_of([cfg.D(0)]))
    xy = reg.cls(span_of([cfg.X[0], cfg.Y[0]]))
    return x, y, s, d, xy


def replay(reg, cert):
    """Exact replay of a certificate's identity sum_r mult_r R_r = sum lambda h(.) - h(x0,y0)
    on the F_3 entropy classes.  Returns (number of non-zero residual classes, unknown rows)."""
    cfg = reg.cfg
    terms = []
    unknown = 0
    for row in cert["rows"]:
        m = Fraction(row["mult"])
        if row["type"] == "sub":
            K = [parse_form(cfg, f) for f in row["K"]]
            t, _ = sub_row(reg, K, parse_form(cfg, row["i"]), parse_form(cfg, row["j"]), False)
        elif row["type"] == "ci":
            t, _ = ci_row(reg, int(row["step"]))
        else:
            unknown += 1
            continue
        for cid, a in t:
            terms.append((cid, m * a))
    x, y, s, d, xy = vertex0(reg)
    lam = cert["lambda"]
    for cid, key in ((x, "1,0"), (y, "0,1"), (s, "1,1")):
        terms.append((cid, -Fraction(lam[key])))
    terms.append((xy, Fraction(1)))
    res = {}
    for cid, a in terms:
        r = reg.find(cid)
        res[r] = res.get(r, Fraction(0)) + a
    bad = {r: v for r, v in res.items() if v != 0}
    return len(bad), unknown, sorted((str(v) for v in bad.values()))[:10]


# ------------------------------------------------------------------ augmentations

def line_readings(cfg, reg):
    seen, out = set(), []
    for v in range(cfg.nv()):
        for f in cfg.readings(v):
            k = span_of([f]).key(reg.kw)
            if k not in seen:
                seen.add(k)
                out.append(f)
    return out


def aug_pairs(reg, cross, cap, rng):
    """K = empty: every pair of distinct reading lines f, g (meet form); with cross=True also
    the two other lines f + g and f - g of span(f, g) against f and g."""
    cfg = reg.cfg
    L = line_readings(cfg, reg)
    pairs = [(a, b) for a in range(len(L)) for b in range(a + 1, len(L))]
    if cap is not None and len(pairs) > cap:
        pairs = rng.sample(pairs, cap)
    rows = []
    for a, b in pairs:
        f, g = L[a], L[b]
        t, spec = sub_row(reg, [], f, g, True)
        rows.append((t, spec))
        if cross:
            for l in (vadd(f, g), vsub(f, g)):
                for h in (f, g):
                    t, spec = sub_row(reg, [], h, l, True)
                    rows.append((t, spec))
    return rows


def aug_neighbours(reg, cert, per_pair, per_add, rng):
    """For each certificate sub row (K, i, j): rows (K, i', j') with i', j' readings of the
    vertices the row touches, (K + f, i, j) and (K - f, i, j); all in meet form."""
    cfg = reg.cfg
    rows = []
    for row in cert["rows"]:
        if row["type"] != "sub":
            continue
        forms = list(row["K"]) + [row["i"], row["j"]]
        verts = sorted(set(int(f[0]) for f in forms))
        R = []
        for v in verts:
            R.extend(cfg.readings(v))
        K = [parse_form(cfg, f) for f in row["K"]]
        i, j = parse_form(cfg, row["i"]), parse_form(cfg, row["j"])
        pr = [(a, b) for a in range(len(R)) for b in range(a + 1, len(R))]
        if len(pr) > per_pair:
            pr = rng.sample(pr, per_pair)
        for a, b in pr:
            rows.append(sub_row(reg, K, R[a], R[b], True))
        add = R if len(R) <= per_add else rng.sample(R, per_add)
        for f in add:
            rows.append(sub_row(reg, K + [f], i, j, True))
        for q in range(len(K)):
            rows.append(sub_row(reg, K[:q] + K[q + 1:], i, j, True))
    return rows


# ------------------------------------------------------------------ LP and exact certificate

KLSS_W = 1.0 - (2.0 / 3.0) / math.log2(3.0)            # 0.5793801642856950 (base 1.88988)
RECORD_W = Fraction(114631769327023765, 209357544569848128)   # 1 / C (Farnamfar Thm 1)


def solve_lp(reg, ge_rows, eq_rows, obj, fixed, sym, uniform):
    """minimize obj.h subject to ge_rows (sum >= 0), eq_rows (sum = 0), 0 <= h <= ub,
    h[fixed] = 1, h equal on the classes in sym.  Returns a dict with the float value and an
    EXACT rational lower bound recomputed from the (rounded) dual solution."""
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix

    nverts = reg.cfg.nv()
    symroots = [reg.find(c) for c in sym]
    symmap = {r: symroots[0] for r in symroots} if symroots else {}
    colmap = {}
    colroots = []

    def col(cid):
        r = reg.find(cid)
        r = symmap.get(r, r)
        c = colmap.get(r)
        if c is None:
            c = colmap[r] = len(colroots)
            colroots.append(r)
        return c

    def compile_rows(rows, sign):
        out, specs = [], []
        for terms, spec in rows:
            d = {}
            for cid, a in terms:
                c = col(cid)
                d[c] = d.get(c, 0) + a
            d = {c: sign * a for c, a in d.items() if a != 0}
            if d:
                out.append(d)
                specs.append(spec)
        return out, specs

    ub_rows, ub_specs = compile_rows(ge_rows, -1)     # -(sum) <= 0
    eq_rows_c, eq_specs = compile_rows(eq_rows, 1)
    cobj = {}
    for cid, a in obj.items():
        c = col(cid)
        cobj[c] = cobj.get(c, Fraction(0)) + Fraction(a)
    fcol = col(fixed)
    n = len(colroots)
    lb = [0] * n
    ub = [nverts] * n
    for r, c in colmap.items():
        if reg.ub[r] == 0:              # the zero subspace: h = 0 in every variant
            ub[c] = 0
        elif uniform and reg.ub[r] < ub[c]:
            ub[c] = reg.ub[r]
    lb[fcol] = 1
    ub[fcol] = 1

    def to_csr(rows):
        data, ri, ci = [], [], []
        for k, d in enumerate(rows):
            for c, a in d.items():
                data.append(float(a))
                ri.append(k)
                ci.append(c)
        return csr_matrix((data, (ri, ci)), shape=(len(rows), n))

    cvec = np.zeros(n)
    for c, a in cobj.items():
        cvec[c] = float(a)
    kw = {}
    if eq_rows_c:
        kw["A_eq"] = to_csr(eq_rows_c)
        kw["b_eq"] = np.zeros(len(eq_rows_c))
    t0 = time.time()
    res = linprog(cvec, A_ub=to_csr(ub_rows), b_ub=np.zeros(len(ub_rows)),
                  bounds=list(zip(lb, ub)), method="highs", **kw)
    out = {"status": int(res.status), "message": str(res.message), "rows_ub": len(ub_rows),
           "rows_eq": len(eq_rows_c), "cols": n, "lp_seconds": round(time.time() - t0, 2)}
    if res.status != 0:
        return out, None
    out["value"] = float(res.fun)
    yu = list(res.ineqlin.marginals)
    ye = list(res.eqlin.marginals) if eq_rows_c else []
    best = None
    for sgn in (1, -1):
        yuf = [min(Fraction(0), Fraction(sgn * y)) if abs(y) > 1e-13 else Fraction(0) for y in yu]
        yef = [Fraction(sgn * y) if abs(y) > 1e-13 else Fraction(0) for y in ye]
        r = dict(cobj)
        for d, y in zip(ub_rows, yuf):
            if y:
                for c, a in d.items():
                    r[c] = r.get(c, Fraction(0)) - y * a
        for d, y in zip(eq_rows_c, yef):
            if y:
                for c, a in d.items():
                    r[c] = r.get(c, Fraction(0)) - y * a
        val = Fraction(0)
        ubused = []
        for c, rv in r.items():
            if rv > 0:
                val += rv * lb[c]
            elif rv < 0:
                val += rv * ub[c]
                if c != fcol:
                    ubused.append((c, rv))
        if best is None or val > best[0]:
            best = (val, sgn, yuf, yef, ubused)
    val, sgn, yuf, yef, ubused = best
    out["lb_exact"] = "%d/%d" % (val.numerator, val.denominator)
    out["lb"] = float(val)
    out["lb_base"] = 3.0 ** float(val)
    out["support_ub"] = sum(1 for y in yuf if y)
    out["support_eq"] = sum(1 for y in yef if y)
    out["ub_bounds_used"] = len(ubused)
    cert = {"lb": val, "ub_rows": [(s, y) for s, y in zip(ub_specs, yuf) if y],
            "eq_rows": [(s, y) for s, y in zip(eq_specs, yef) if y],
            "ub_used": [(colroots[c], rv, ub[c]) for c, rv in ubused]}
    return out, cert


def export_cert(reg, cert, path, meta):
    m = reg.cfg.nsym

    def vd(v):
        return to_digits(v, m)

    def spec(s):
        if s[0] == "ci":
            return {"type": "ci", "step": s[1]}
        if s[0] == "mono":
            return {"type": "mono", "K": [vd(v) for v in s[1]], "i": vd(s[2]), "j": vd(s[3]),
                    "which": s[4]}
        return {"type": s[0], "K": [vd(v) for v in s[1]], "i": vd(s[2]), "j": vd(s[3])}

    def fr(q):
        return "%d/%d" % (q.numerator, q.denominator)

    doc = {"meta": meta, "nsym": m,
           "X": [vd(v) for v in reg.cfg.X], "Y": [vd(v) for v in reg.cfg.Y],
           "lb": fr(cert["lb"]),
           "ge_rows": [dict(spec(s), mult=fr(-y)) for s, y in cert["ub_rows"]],
           "eq_rows": [dict(spec(s), mult=fr(y)) for s, y in cert["eq_rows"]],
           "ub_used": [{"gens": [vd(v) for v in reg.ubspan[r]], "bound": b, "r": fr(rv)}
                       for r, rv, b in cert["ub_used"]]}
    with open(path, "w") as fh:
        json.dump(doc, fh)


# ------------------------------------------------------------------ driver

BASE = "https://arxiv.org/src/2611.19594v1/anc/certificates/"
CERTS = ["standard-five-page.json", "standard.json"]


def load_cert(name, data_dir):
    if data_dir and os.path.isdir(data_dir):
        for root, _dirs, files in os.walk(data_dir):
            if name in files:
                with open(os.path.join(root, name), "rb") as fh:
                    raw = fh.read()
                return json.loads(raw.decode("utf-8")), hashlib.sha256(raw).hexdigest(), "data"
    req = urllib.request.Request(BASE + name, headers={"User-Agent": "f3cert-replay/1.0"})
    raw = urllib.request.urlopen(req, timeout=180).read()
    try:
        if data_dir:
            os.makedirs(data_dir, exist_ok=True)
            with open(os.path.join(data_dir, name), "wb") as fh:
                fh.write(raw)
    except OSError:
        pass
    return json.loads(raw.decode("utf-8")), hashlib.sha256(raw).hexdigest(), "fetched"


def run_config(name, cert, out_dir, log, budget, rng):
    t0 = time.time()
    cfg = build_config(cert["steps"])
    reg = Registry(cfg)
    rep = {"vertices": cfg.nv(), "symbols": cfg.nsym, "steps": len(cfg.steps)}
    if cert.get("rows"):
        rep["eqlaw_applied"], rep["eqlaw_skipped"] = apply_eqlaw(reg, cert)
        nbad, unknown, sample = replay(reg, cert)
        rep["replay_nonzero_classes"] = nbad
        rep["replay_unknown_rows"] = unknown
        rep["replay_residual_sample"] = sample
        rep["claimed_C"] = cert.get("claimed_C")
        log("%s: replay nonzero=%d unknown=%d" % (name, nbad, unknown))
    x, y, s, d, xy = vertex0(reg)
    cert_plain, cert_meet, cert_mono = [], [], []
    for row in cert.get("rows", []):
        if row["type"] != "sub":
            continue
        K = [parse_form(cfg, f) for f in row["K"]]
        i, j = parse_form(cfg, row["i"]), parse_form(cfg, row["j"])
        cert_plain.append(sub_row(reg, K, i, j, False))
        cert_meet.append(sub_row(reg, K, i, j, True))
        cert_mono.extend(mono_rows(reg, K, i, j))
    ci = [ci_row(reg, k) for k in range(len(cfg.steps))]
    base_pairs = sub_row(reg, [], cfg.X[0], cfg.Y[0], True)
    rep["classes_cert"] = len(reg.parent)
    aug = []
    if time.time() - t0 < budget:
        small = cfg.nv() <= 40
        aug.extend(aug_pairs(reg, cross=small, cap=None if small else 25000, rng=rng))
        log("%s: pair rows %d (%.0fs)" % (name, len(aug), time.time() - t0))
    if time.time() - t0 < budget and cert.get("rows"):
        aug.extend(aug_neighbours(reg, cert, per_pair=30 if cfg.nv() <= 40 else 12,
                                  per_add=10 if cfg.nv() <= 40 else 6, rng=rng))
        log("%s: +neighbour rows, total aug %d (%.0fs)" % (name, len(aug), time.time() - t0))
    rep["aug_rows"] = len(aug)
    rep["classes_total"] = len(reg.parent)
    rep["build_seconds"] = round(time.time() - t0, 1)
    sym = [x, y, s]
    variants = []
    if cert.get("lambda"):
        lam = cert["lambda"]
        variants.append(("cert-lambda-plain", cert_plain, {x: Fraction(lam["1,0"]),
                         y: Fraction(lam["0,1"]), s: Fraction(lam["1,1"])}, [], False))
    core = cert_plain + cert_meet + cert_mono + [base_pairs]
    variants += [
        ("cert-sym-plain", cert_plain, {x: 1}, sym, False),
        ("cert-sym-meet", core, {x: 1}, sym, False),
        ("cert-sym-meet-unif", core, {x: 1}, sym, True),
        ("aug-sym-meet", core + aug, {x: 1}, sym, False),
        ("aug-sym-meet-unif", core + aug, {x: 1}, sym, True),
    ]
    rep["variants"] = {}
    best = None
    for vname, ge, obj, sy, uni in variants:
        if not ge:
            continue
        try:
            info, c = solve_lp(reg, ge, ci, obj, d, sy, uni)
        except Exception as exc:  # report, never hide
            info, c = {"error": repr(exc)}, None
        rep["variants"][vname] = info
        log("%s %s: %s" % (name, vname, json.dumps(info)))
        if c is not None and sy and (best is None or c["lb"] > best[1]["lb"]):
            best = (vname, c)
    if best is not None:
        path = os.path.join(out_dir, "cert_%s_%s.json" % (name.replace(".json", ""), best[0]))
        export_cert(reg, best[1], path, {"config": name, "variant": best[0],
                                         "objective": "h(x0)=h(y0)=h(s0), h(d0)=1"})
        rep["best_variant"] = best[0]
        rep["best_lb"] = float(best[1]["lb"])
        rep["best_lb_exact"] = "%d/%d" % (best[1]["lb"].numerator, best[1]["lb"].denominator)
        rep["best_base"] = 3.0 ** float(best[1]["lb"])
    return rep


def verdict(reports):
    worst = []
    out = "NO_GAIN"
    for name, rep in reports.items():
        if "error" in rep:
            worst.append("ERROR")
            continue
        v = rep.get("variants", {})
        ctl = v.get("cert-lambda-plain")
        if rep.get("replay_nonzero_classes", 0) or (ctl and ctl.get("lb", 0) < 1 - 1e-9):
            worst.append("CONTROL_FAIL")
        for vn, info in v.items():
            if vn != "cert-lambda-plain" and info.get("lb", 0) > KLSS_W + 1e-9:
                worst.append("UNSOUND")
        bl = rep.get("best_lb")
        if bl is not None:
            if Fraction(rep["best_lb_exact"]) > RECORD_W:
                out = "F3_RECORD"
            elif out != "F3_RECORD":
                claimed = rep.get("claimed_C")
                own = 1 / Fraction(claimed) if claimed else Fraction(1, 2)
                if Fraction(rep["best_lb_exact"]) > own and out == "NO_GAIN":
                    out = "F3_GAIN"
    for w in ("UNSOUND", "CONTROL_FAIL", "ERROR"):
        if w in worst:
            return w + "+" + out
    return out


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--data-dir", default="data")
    ap.add_argument("--budget", type=float, default=2400.0)
    ap.add_argument("--only", default="")
    a = ap.parse_args(argv)
    os.makedirs(a.out_dir, exist_ok=True)
    logf = open(os.path.join(a.out_dir, "log.txt"), "a")

    def log(msg):
        line = "[%s] %s" % (time.strftime("%H:%M:%S"), msg)
        print(line, flush=True)
        logf.write(line + "\n")
        logf.flush()

    rng = random.Random(20261127)
    reports, sources = {}, {}
    todo = [("tomar-page", {"steps": TOMAR_PAGE}, None)]
    for nm in CERTS:
        if a.only and a.only != nm:
            continue
        try:
            cert, sha, how = load_cert(nm, a.data_dir)
            todo.append((nm, cert, sha))
            sources[nm] = {"sha256": sha, "how": how, "url": BASE + nm}
        except Exception as exc:
            reports[nm] = {"error": "load: " + repr(exc)}
            log("load %s failed: %r" % (nm, exc))
    for nm, cert, _sha in todo:
        try:
            reports[nm] = run_config(nm, cert, a.out_dir, log, a.budget, rng)
        except Exception as exc:
            import traceback
            reports[nm] = {"error": repr(exc), "trace": traceback.format_exc()[-2000:]}
            log("config %s failed: %r" % (nm, exc))
        with open(os.path.join(a.out_dir, "results.json"), "w") as fh:
            json.dump({"sources": sources, "reports": reports}, fh, indent=1)
    v = verdict({k: r for k, r in reports.items() if k != "tomar-page"})
    summary = {"verdict": v, "record_w": float(RECORD_W), "record_base": 3.0 ** float(RECORD_W),
               "klss_w": KLSS_W, "sources": sources, "reports": reports}
    with open(os.path.join(a.out_dir, "results.json"), "w") as fh:
        json.dump(summary, fh, indent=1)
    lines = ["VERDICT %s" % v]
    for nm, rep in reports.items():
        lines.append("%s: best=%s lb=%s base=%s replay_nonzero=%s" % (
            nm, rep.get("best_variant"), rep.get("best_lb"), rep.get("best_base"),
            rep.get("replay_nonzero_classes")))
        for vn, info in rep.get("variants", {}).items():
            lines.append("  %-20s value=%s lb=%s rows=%s cols=%s" % (
                vn, info.get("value"), info.get("lb"), info.get("rows_ub"), info.get("cols")))
    with open(os.path.join(a.out_dir, "summary.txt"), "w") as fh:
        fh.write("\n".join(lines) + "\n")
    log("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
