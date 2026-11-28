# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Independent Kakeya check in F_q^3 (shares no code with slices.py).

F_4 here is built from discrete logarithms: the non-zero elements are g^0, g^1, g^2 with
g = a (code 2), g^2 = a + 1 (code 3); codes 0, 1, 2, 3 as in slices.py (bit vectors of
b1 * a + b0).  Addition is XOR of codes.  Prime q uses integers mod q."""
import itertools

_LOG4 = {1: 0, 2: 1, 3: 2}
_EXP4 = [1, 2, 3]


def _mul4(x, y):
    if x == 0 or y == 0:
        return 0
    return _EXP4[(_LOG4[x] + _LOG4[y]) % 3]


def ops(q):
    if q == 4:
        return (lambda x, y: x ^ y), _mul4
    if q in (2, 3, 5, 7):
        return (lambda x, y: (x + y) % q), (lambda x, y: (x * y) % q)
    raise ValueError(q)


def is_kakeya3(K, q):
    """True if K (iterable of 3-tuples over F_q) contains a full line in every direction; checks
    every non-zero vector, not only normalised ones."""
    add, mul = ops(q)
    S = set(tuple(p) for p in K)
    for p in S:
        if len(p) != 3 or any(not 0 <= c < q for c in p):
            return False, "bad point %r" % (p,)
    for d in itertools.product(range(q), repeat=3):
        if not any(d):
            continue
        ok = False
        for a in S:
            if all(tuple(add(a[k], mul(t, d[k])) for k in range(3)) in S for t in range(q)):
                ok = True
                break
        if not ok:
            return False, "no line in direction %r" % (d,)
    return True, "ok"


def kss_set_q4():
    """The 28-point Kakeya set of F_4^3 from the Kopparty-Saraf-Sudan even-q construction:
    the plane t = 0 together with {(b t + b^2, c t + c^2, t) : t != 0}, b, c in F_4."""
    add, mul = ops(4)
    pts = set()
    for x in range(4):
        for y in range(4):
            pts.add((x, y, 0))
    for b in range(4):
        for c in range(4):
            for t in range(1, 4):
                pts.add((add(mul(b, t), mul(b, b)), add(mul(c, t), mul(c, c)), t))
    return sorted(pts)


def plane_min(K, q):
    """Smallest number of points of K on any plane of F_q^3 (planes a.x = b, a normalised)."""
    add, mul = ops(q)
    S = [tuple(p) for p in K]
    best = None
    for a in itertools.product(range(q), repeat=3):
        if not any(a):
            continue
        first = next(c for c in a if c)
        if first != 1:
            continue
        counts = [0] * q
        for p in S:
            v = 0
            for k in range(3):
                v = add(v, mul(a[k], p[k]))
            counts[v] += 1
        m = min(counts)
        if best is None or m < best:
            best = m
    return best
