"""sparse_cert_check.py -- independent exact checks for the sparse Kakeya LP over F_3.

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only; every number is an exact Fraction.

Two checks, sharing no code with kakeya_lp.py or kakeya_sparse.py (only the basic F_3
helpers of kakeya_cert_check.py: Subspace, span_closure, lin, read, ext):

check(cert)        a "kakeya-sparse-certificate-1" found by kakeya_sparse.py. The
                   configuration is rebuilt from the word, every row is recomputed from its
                   description (forms are explicit combinations of vertex readings), the rows
                   are added with their multipliers, and every entropy term must cancel.
                   A pass proves, for every map P of every F_3^k with X uniform,
                   (H(P(X)) + H(P(X) + X) + H(2P(X) + X)) / 3 >= bound * log|F_3^k|,
                   hence every Kakeya set K in F_3^n has |K| >= 3^(bound * n - o(n)).

farn_replay(cert)  one of A. Farnamfar's standard-form certificates (arXiv:2611.19594,
                   ancillary files; fields steps / eqlaw / rows / lambda), replayed in F_3:
                   sum_r m_r R_r - (a h(x0) + b h(y0) + c h(s0) - h(x0, y0)) must vanish
                   modulo his equal-law generators. A pass proves
                   H(X, Y) <= a H(X) + b H(Y) + c H(X + Y) for every Kakeya pair over F_3,
                   i.e. the Kakeya bound with exponent 1 / (a + b + c).

Usage: python sparse_cert_check.py cert.json [more.json ...]
"""

import json
import sys
from fractions import Fraction

from kakeya_cert_check import Subspace, ext, lin, read, span_closure  # noqa: F401


def _phi_factory(G, kap, r0):
    """phi(u) = (g, cs) written as g + cs, where u = g + sum cs_j kap_j and g lies in G."""
    m = len(kap)
    ech = []
    for j, k in enumerate(kap):
        v = G.residue(ext(k, r0))
        tag = [0] * m
        tag[j] = 1
        for ev, et, p in ech:
            c = v[p]
            if c:
                v = [(a - c * b) % 3 for a, b in zip(v, ev)]
                tag = [(a - c * b) % 3 for a, b in zip(tag, et)]
        assert any(v), "copied coordinates are dependent"
        p = min(i for i, a in enumerate(v) if a)
        if v[p] == 2:
            v = [(2 * a) % 3 for a in v]
            tag = [(2 * a) % 3 for a in tag]
        ech.append((v, tag, p))

    def phi(u):
        u = ext(u, r0)
        w = G.residue(u)
        cs = [0] * m
        for ev, et, p in ech:
            c = w[p]
            if c:
                w = [(a - c * b) % 3 for a, b in zip(w, ev)]
                cs = [(a + c * b) % 3 for a, b in zip(cs, et)]
        assert not any(w), "form is not a function of the copied block"
        g = u
        for c, kv in zip(cs, kap):
            if c:
                g = lin((1, g), ((3 - c) % 3, ext(kv, r0)))
        assert G.has(g), "decomposition failed"
        return tuple(g) + tuple(cs)

    return phi


def rebuild(word):
    """Returns (R, X, Y, steps) with vertex readings padded to the final R."""
    R = 2
    X = [(1, 0)]
    Y = [(0, 1)]
    steps = []
    for st in word["steps"]:
        block = [int(v) for v in st["block"]]
        glue = [(int(g[0]), str(g[1])) for g in st["glue"]]
        assert block and len(set(block)) == len(block), "bad block"
        assert all(0 <= v < len(X) for v in block), "block vertex does not exist"
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
        assert kap, "trivial copy"
        phi = _phi_factory(G, kap, r0)
        old_n = len(X)
        new = []
        for x, y in zip(bx, by):
            X.append(phi(x))
            Y.append(phi(y))
            new.append(len(X) - 1)
        R = r0 + len(kap)
        steps.append({"block": block, "glue": glue, "gforms": gforms, "old_n": old_n,
                      "new": new})
    X = [ext(x, R) for x in X]
    Y = [ext(y, R) for y in Y]
    return R, X, Y, steps


def cvec(X, Y, R, combo):
    out = (0,) * R
    for t in combo:
        v, a, b = int(t[0]), int(t[1]), int(t[2])
        assert 0 <= v < len(X), "form on a missing vertex"
        out = lin((1, out), (a % 3, X[v]), (b % 3, Y[v]))
    return out


class _Keys:
    def __init__(self, R, pairs):
        self.R = R
        self.pairs = pairs
        self.cache = {}

    def __call__(self, vecs):
        sig = tuple(sorted(set(ext(f, self.R) for f in vecs)))
        if sig not in self.cache:
            self.cache[sig] = span_closure(list(sig), self.pairs, self.R).key()
        return self.cache[sig]


def check(cert):
    """Return the proved bound (Fraction) or raise AssertionError."""
    assert cert.get("format") == "kakeya-sparse-certificate-1", "unknown format"
    R, X, Y, steps = rebuild(cert["word"])
    pairs = list(zip(X, Y))
    K = _Keys(R, pairs)

    def V(combos):
        return [cvec(X, Y, R, c) for c in combos]

    total = {}
    tco = Fraction(0)
    const = Fraction(0)
    for row in cert["rows"]:
        d = row["d"]
        mu = Fraction(row["m"])
        kind = d["k"]
        tc = 0
        c0 = 0
        if kind == "sub":
            Kc, i, j = V(d["K"]), V([d["i"]]), V([d["j"]])
            terms = [(K(Kc + i), 1), (K(Kc + j), 1), (K(Kc + i + j), -1), (K(Kc), -1)]
            sense = "ge"
        elif kind == "mono":
            Kc, i = V(d["K"]), V([d["i"]])
            terms = [(K(Kc + i), 1), (K(Kc), -1)]
            sense = "ge"
        elif kind == "copy":
            st = steps[int(d["step"])]
            old = [u for v in range(st["old_n"]) for u in pairs[v]]
            new = [u for v in st["new"] for u in pairs[v]]
            terms = [(K(old + new), 1), (K(st["gforms"]), 1), (K(old), -1), (K(new), -1)]
            sense = "eq"
        elif kind == "law":
            st = steps[int(d["step"])]
            m = dict(zip(st["block"], st["new"]))
            src, img = [], []
            for c in d["S"]:
                tri = [(int(t[0]), int(t[1]), int(t[2])) for t in c]
                assert all(v in m for v, _, _ in tri), "law: form outside the copied block"
                src.append(cvec(X, Y, R, tri))
                img.append(cvec(X, Y, R, [(m[v], a, b) for v, a, b in tri]))
            terms = [(K(src), 1), (K(img), -1)]
            sense = "eq"
        elif kind == "norm":
            terms = [(K(list(pairs[int(d["v"])])), 1)]
            c0 = -1
            sense = "eq"
        elif kind == "read":
            assert d["r"] in ("x", "y", "s"), "read: bad reading"
            x, y = pairs[int(d["v"])]
            terms = [(K([read(x, y, d["r"])]), 1)]
            tc = -1
            sense = "eq"
        elif kind == "unif":
            assert cert.get("uniform"), "unif row in a certificate without the Kakeya flag"
            terms = [(K(V([d["f"]])), -1)]
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
    total.pop((), None)
    left = [k for k, v in total.items() if v != 0]
    assert not left, "%d entropy terms do not cancel" % len(left)
    assert tco > 0, "no positive multiple of t"
    bound = -const / tco
    if "claimed_bound" in cert:
        assert Fraction(cert["claimed_bound"]) == bound, "claimed bound differs"
    return bound


# ----------------------------------------------------------------------------------------
# Farnamfar's standard-form certificates, replayed in F_3
# ----------------------------------------------------------------------------------------


def _slope_kind(a, b):
    a, b = int(a) % 3, int(b) % 3
    assert (a, b) != (0, 0), "zero slope"
    lead = a if a else b
    if lead == 2:
        a, b = (2 * a) % 3, (2 * b) % 3
    return {(1, 0): "x", (0, 1): "y", (1, 1): "s", (1, 2): "d"}[(a, b)]


def _farn_tri(f):
    assert (isinstance(f, list) and len(f) == 2 and isinstance(f[0], int)
            and not isinstance(f[0], bool) and isinstance(f[1], list) and len(f[1]) == 2), \
        "unsupported form %r" % (f,)
    return (f[0], int(f[1][0]) % 3, int(f[1][1]) % 3)


def farn_replay(cert):
    """Replay in F_3. Returns a dict; "ok" is True only if every class cancels."""
    assert not cert.get("extra"), "extra (cross) forms are not supported"
    word = {"steps": [{"block": [int(u) for u in st["U"]],
                       "glue": [[int(v), _slope_kind(sl[0], sl[1])] for v, sl in st["V"]]}
                      for st in cert["steps"]]}
    R, X, Y, steps = rebuild(word)
    pairs = list(zip(X, Y))
    K = _Keys(R, pairs)

    def V(forms):
        return [cvec(X, Y, R, [_farn_tri(f)]) for f in forms]

    lam = {}
    for kk, vv in cert["lambda"].items():
        a, b = [int(z) for z in kk.split(",")]
        lam[(a % 3, b % 3)] = lam.get((a % 3, b % 3), Fraction(0)) + Fraction(vv)

    parent = {}

    def find(k):
        parent.setdefault(k, k)
        while parent[k] != k:
            parent[k] = parent[parent[k]]
            k = parent[k]
        return k

    for e in cert.get("eqlaw", []):
        st = steps[int(e["step"])]
        m = dict(zip(st["block"], st["new"]))
        src, img = [], []
        for f in e["gens"]:
            v, a, b = _farn_tri(f)
            assert v in m, "eqlaw form outside the copied block"
            src.append(cvec(X, Y, R, [(v, a, b)]))
            img.append(cvec(X, Y, R, [(m[v], a, b)]))
        ra, rb = find(K(src)), find(K(img))
        if ra != rb:
            parent[ra] = rb

    tried = {}
    for ci_sign in (1, -1):
        total = {}

        def add(k, c):
            total[k] = total.get(k, Fraction(0)) + c

        for row in cert["rows"]:
            mu = Fraction(row["mult"])
            typ = row["type"]
            if typ == "sub":
                assert mu >= 0, "negative multiplier on a sub row"
                Kc, i, j = V(row["K"]), V([row["i"]]), V([row["j"]])
                add(K(Kc + i), mu)
                add(K(Kc + j), mu)
                add(K(Kc + i + j), -mu)
                add(K(Kc), -mu)
            elif typ == "mono":
                assert mu >= 0, "negative multiplier on a mono row"
                Kc, i = V(row["K"]), V([row["i"]])
                add(K(Kc + i), mu)
                add(K(Kc), -mu)
            elif typ == "ci":
                st = steps[int(row["step"])]
                old = [u for v in range(st["old_n"]) for u in pairs[v]]
                new = [u for v in st["new"] for u in pairs[v]]
                sm = ci_sign * mu
                add(K(old + new), sm)
                add(K(st["gforms"]), sm)
                add(K(old), -sm)
                add(K(new), -sm)
            else:
                raise AssertionError("unsupported row type %r" % (typ,))
        for (a, b), c in lam.items():
            add(K([cvec(X, Y, R, [(0, a, b)])]), -c)
        add(K(list(pairs[0])), Fraction(1))
        cls = {}
        for k, c in total.items():
            if k == ():
                continue
            r = find(k)
            cls[r] = cls.get(r, Fraction(0)) + c
        bad = sum(1 for c in cls.values() if c != 0)
        if bad == 0:
            S = sum(lam.values())
            claimed = cert.get("claimed_C")
            return {"ok": True, "ci_sign": ci_sign, "C": str(S), "C_float": float(S),
                    "bound": str(1 / S), "bound_float": float(1 / S),
                    "base": 3 ** float(1 / S), "claimed_C": claimed,
                    "claim_matches": claimed is None or Fraction(claimed) == S,
                    "rows": len(cert["rows"]), "eqlaw": len(cert.get("eqlaw", [])),
                    "vertices": len(X), "R": R}
        tried[str(ci_sign)] = bad
    return {"ok": False, "uncancelled_classes": tried, "vertices": len(X), "R": R}


def main(argv):
    ok = True
    for path in argv:
        with open(path) as fh:
            cert = json.load(fh)
        try:
            if cert.get("format") == "kakeya-sparse-certificate-1":
                b = check(cert)
                print("%s: PASS, bound %s = %.9f, base 3^bound = %.6f" % (path, b, float(b),
                                                                         3 ** float(b)))
            else:
                r = farn_replay(cert)
                ok = ok and r["ok"]
                print("%s: %s" % (path, json.dumps(r)))
        except AssertionError as e:
            ok = False
            print("%s: FAIL (%s)" % (path, e))
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
