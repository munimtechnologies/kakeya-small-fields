# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Independent Kakeya check for point sets in F_q^n (shares no code with kq.py).

Elements of F_4 are coded 0..3 as the bit vectors of polynomials b1*a + b0 over F_2 with
a^2 = a + 1 (the code used by kq.py); arithmetic here is carry-less multiplication followed by
reduction modulo x^2 + x + 1.  Prime q uses integers mod q.

is_kakeya(K, n, q) tests EVERY non-zero vector d (not only normalised ones): some a in K has
a + t d in K for all t in F_q."""
import itertools


def _gf2_mul(x, y, poly=0b111, deg=2):
    r = 0
    while y:
        if y & 1:
            r ^= x
        y >>= 1
        x <<= 1
        if x >> deg & 1:
            x ^= poly
    return r


def ops(q):
    if q == 4:
        return (lambda x, y: x ^ y), _gf2_mul
    if q in (2, 3, 5, 7):
        return (lambda x, y: (x + y) % q), (lambda x, y: (x * y) % q)
    raise ValueError(q)


def is_kakeya(K, n, q):
    add, mul = ops(q)
    S = set(tuple(p) for p in K)
    for p in S:
        if len(p) != n or any(not 0 <= c < q for c in p):
            return False, "bad point %r" % (p,)
    for d in itertools.product(range(q), repeat=n):
        if not any(d):
            continue
        found = False
        for a in S:
            if all(tuple(add(ai, mul(t, di)) for ai, di in zip(a, d)) in S for t in range(q)):
                found = True
                break
        if not found:
            return False, "no line in direction %r" % (d,)
    return True, "ok"


def field_axioms_ok(q):
    """Sanity check of the arithmetic: a field with q elements."""
    add, mul = ops(q)
    E = range(q)
    for x in E:
        for y in E:
            for z in E:
                if mul(x, add(y, z)) != add(mul(x, y), mul(x, z)):
                    return False
                if mul(mul(x, y), z) != mul(x, mul(y, z)):
                    return False
    for x in E:
        if x and not any(mul(x, y) == 1 for y in E):
            return False
    return True
