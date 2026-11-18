"""kakeya_cert_check.py -- independent exact checker for Kakeya-LP certificates.

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only; every number is an exact Fraction.

This file shares no code with kakeya_lp.py. It rebuilds the configuration from the word
with its own F_3 linear algebra, recomputes every row of the certificate from its
description, adds the rows with their multipliers and checks that every entropy term
cancels. What a passing certificate proves (see kakeya_lp.py, "Rotation"):

    for every k, every map a: F_3^k -> F_3^k and D uniform on F_3^k, with
    x = a(D), y = a(D) + D, s = x + y:   (H(x) + H(y) + H(s)) / 3 >= bound * log|F_3^k|,

and hence every Kakeya set K in F_3^n has |K| >= 3^(bound * n).

Usage: python kakeya_cert_check.py cert.json [more.json ...]
"""

import json
import sys
from fractions import Fraction


class Subspace:
    """Subspace of F_3^R kept as {pivot: row}, fully reduced (each row has a 1 at its
    pivot and 0 at every other pivot)."""

    def __init__(self, R):
        self.R = R
        self.rows = {}

    def clone(self):
        s = Subspace(self.R)
        s.rows = dict(self.rows)
        return s

    def residue(self, v):
        v = [a % 3 for a in v]
        for p in sorted(self.rows):
            c = v[p]
            if c:
                row = self.rows[p]
                v = [(a - c * b) % 3 for a, b in zip(v, row)]
        return v

    def has(self, v):
        return not any(self.residue(v))

    def insert(self, v):
        w = self.residue(v)
        if not any(w):
            return False
        p = min(i for i, a in enumerate(w) if a)
        if w[p] == 2:
            w = [(2 * a) % 3 for a in w]
        for q in list(self.rows):
            row = self.rows[q]
            c = row[p]
            if c:
                self.rows[q] = tuple((a - c * b) % 3 for a, b in zip(row, w))
        self.rows[p] = tuple(w)
        return True

    def key(self):
        return tuple(self.rows[p] for p in sorted(self.rows))


def ext(u, R):
    u = tuple(a % 3 for a in u)
    if len(u) > R:
        assert not any(u[R:]), "form too long"
        return u[:R]
    return u + (0,) * (R - len(u))


def lin(*pairs):
    """lin((c1, u1), (c2, u2), ...) = sum c_i u_i over F_3."""
    n = len(pairs[0][1])
    out = [0] * n
    for c, u in pairs:
        for i in range(n):
            out[i] = (out[i] + c * u[i]) % 3
    return tuple(out)


def read(x, y, kind):
    if kind == "x":
        return x
    if kind == "y":
        return y
    if kind == "s":
        return lin((1, x), (1, y))
    if kind == "d":
        return lin((1, y), (2, x))
    raise ValueError("unknown reading %r" % (kind,))


def span_closure(forms, pairs, R):
    S = Subspace(R)
    for f in forms:
        S.insert(ext(f, R))
    grown = True
    while grown:
        grown = False
        for x, y in pairs:
            if S.has(read(x, y, "d")) and not S.has(x):
                S.insert(x)
                grown = True
    return S


def rebuild(word):
    """Returns (R, X, Y, steps); X, Y are the vertex readings padded to the final R."""
    R = 2
    X = [(1, 0)]
    Y = [(0, 1)]
    steps = []
    for st in word["steps"]:
        block = list(st["block"])
        glue = [tuple(g) for g in st["glue"]]
        assert block and len(set(block)) == len(block), "bad block"
        r0 = R
        bx = [ext(X[v], r0) for v in block]
        by = [ext(Y[v], r0) for v in block]
        where = {v: i for i, v in enumerate(block)}
        gforms = []
        for v, k in glue:
            assert v in where, "glue outside the block"
            gforms.append(read(bx[where[v]], by[where[v]], k))
        G = span_closure(gforms, list(zip(bx, by)), r0)
        cur = G.clone()
        kap = []
        for x, y in zip(bx, by):
            for u in (x, y):
                if not cur.has(u):
                    kap.append(u)
                    cur.insert(u)
        m = len(kap)
        assert m > 0, "trivial copy"
        coeff_list = [()]
        for _ in range(m):
            coeff_list = [c + (a,) for c in coeff_list for a in range(3)]

        def phi(u, G=G, kap=kap, m=m, r0=r0, coeff_list=coeff_list):
            u = ext(u, r0)
            for cs in coeff_list:
                g = u
                for c, kv in zip(cs, kap):
                    if c:
                        g = lin((1, g), ((3 - c) % 3, kv))
                if G.has(g):
                    return g + tuple(cs)
            raise AssertionError("form is not a function of the copied block")

        old_n = len(X)
        new = []
        for x, y in zip(bx, by):
            X.append(phi(x))
            Y.append(phi(y))
            new.append(len(X) - 1)
        R = r0 + m
        steps.append({"block": block, "glue": glue, "gforms": gforms, "phi": phi,
                      "r0": r0, "old_n": old_n, "new": new})
    X = [ext(x, R) for x in X]
    Y = [ext(y, R) for y in Y]
    return R, X, Y, steps


def atom_list(R, X, Y, steps, extras):
    out, seen = [], set()

    def put(f):
        f = ext(f, R)
        if any(f) and f not in seen:
            seen.add(f)
            out.append(f)

    for x, y in zip(X, Y):
        put(x)
        put(y)
    for st in steps:
        for v, k in st["glue"]:
            if k != "d":
                put(read(X[v], Y[v], k))
    for comb in extras:
        f = (0,) * R
        for v, k, c in comb:
            f = lin((1, f), (c % 3, read(X[v], Y[v], k)))
        put(f)
    return out


def check(cert):
    """Return the proved bound (Fraction) or raise AssertionError."""
    assert cert.get("format") == "kakeya-lp-certificate-1", "unknown format"
    R, X, Y, steps = rebuild(cert["word"])
    atoms = atom_list(R, X, Y, steps, cert.get("extras", []))
    given = [tuple(f) for _, f in cert["atoms"]]
    assert given == atoms, "atom list does not match the word"
    pairs = list(zip(X, Y))
    cache = {}

    def K(forms):
        sig = tuple(sorted(set(ext(f, R) for f in forms)))
        if sig not in cache:
            cache[sig] = span_closure(list(sig), pairs, R).key()
        return cache[sig]

    def A(ids):
        return [atoms[i] for i in ids]

    total = {}
    tco = Fraction(0)
    const = Fraction(0)
    for row in cert["rows"]:
        d = row["d"]
        mu = Fraction(row["m"])
        kind = d["k"]
        tc = 0
        c0 = 0
        if kind in ("sub", "mi", "mono"):
            if kind == "sub":
                a_, b_, c_ = [d["i"]], [d["j"]], list(d["K"])
            elif kind == "mi":
                a_, b_, c_ = list(d["A"]), list(d["B"]), list(d["C"])
            else:
                a_, b_, c_ = [d["i"]], [], list(d["K"])
            if kind == "mono":
                terms = [(K(A(a_ + c_)), 1), (K(A(c_)), -1)]
            else:
                terms = [(K(A(a_ + c_)), 1), (K(A(b_ + c_)), 1),
                         (K(A(a_ + b_ + c_)), -1), (K(A(c_)), -1)]
            sense = "ge"
        elif kind == "copy":
            st = steps[d["step"]]
            old = [u for v in range(st["old_n"]) for u in pairs[v]]
            new = [u for v in st["new"] for u in pairs[v]]
            terms = [(K(old + new), 1), (K(st["gforms"]), 1), (K(old), -1), (K(new), -1)]
            sense = "eq"
        elif kind == "law":
            st = steps[d["step"]]
            src = A(d["S"])
            img = []
            for f in src:
                assert not any(f[st["r0"]:]), "law: atom outside the copied block"
                img.append(st["phi"](f[:st["r0"]]))
            terms = [(K(src), 1), (K(img), -1)]
            sense = "eq"
        elif kind == "norm":
            terms = [(K(list(pairs[d["v"]])), 1)]
            c0 = -1
            sense = "eq"
        elif kind == "read":
            assert d["r"] in ("x", "y", "s"), "read: bad reading"
            x, y = pairs[d["v"]]
            terms = [(K([read(x, y, d["r"])]), 1)]
            tc = -1
            sense = "eq"
        elif kind == "unif":
            assert cert.get("uniform"), "unif row in a certificate without the Kakeya flag"
            terms = [(K([atoms[d["i"]]]), -1)]
            c0 = 1
            sense = "ge"
        else:
            raise AssertionError("unknown row kind %r" % (kind,))
        if sense == "ge":
            assert mu >= 0, "negative multiplier on an inequality"
        for key, c in terms:
            total[key] = total.get(key, Fraction(0)) + mu * c
        tco += mu * tc
        const += mu * c0
    total.pop((), None)  # the empty set has entropy 0
    left = [k for k, v in total.items() if v != 0]
    assert not left, "%d entropy terms do not cancel" % len(left)
    assert tco > 0, "no positive multiple of t"
    bound = -const / tco
    if "claimed_bound" in cert:
        assert Fraction(cert["claimed_bound"]) == bound, "claimed bound differs"
    return bound


def main(argv):
    ok = True
    for path in argv:
        with open(path) as fh:
            cert = json.load(fh)
        try:
            b = check(cert)
            print("%s: PASS, bound %s = %.6f, base 3^bound = %.6f" % (path, b, float(b),
                                                                      3 ** float(b)))
        except AssertionError as e:
            ok = False
            print("%s: FAIL (%s)" % (path, e))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
