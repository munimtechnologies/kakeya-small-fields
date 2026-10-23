# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m93: the orbits of 3-dimensional commutative subspaces of M_4(F_2) under conjugation, and
which of them meet the conditions that Lemmas 38 and 94 put on the space {M_n : n in N_Y} of an
element of rank 4 at t = 8 and dim V = 11 (notes/a84.md, a85.md; cube_groups/m93-predictions.md).

Why: by Corollary 121 an element u of rank 4 at (8, 11) is in Case B in shape (c), and by Lemma 39
(notes/shape-c.md) the matrices M_n (n in N_Y, a space of dimension 3) can be moved by simultaneous
conjugation in GL_4(F_2) and by recombination in GL_3(F_2). As n -> M_n is one-to-one on N
(Corollary 121) and M_u = I, the space W = span{M_n : n in N_Y} is a 3-dimensional space of
pairwise commuting 4 x 4 matrices that does not contain I, and the tuple's orbit is the orbit of W
under conjugation. A machine search of rank 4 at (8, 4) would split by these orbits, so this job
counts them first, with the conditions each must meet (all necessary, none sufficient):

    singular  every non-zero matrix of W is singular (Lemma 94(b), types (N4) and (F3));
    n4        singular, and one may pick for each non-zero M in W a vector q_M != 0 with M q_M = 0
              so that the seven picks span a space of dimension at least 3 (Lemma 94(b) and
              Lemma 38(e) with D = F_2^4: type (N4), d = 4);
    f3        singular, and for some hyperplane D invariant under W the picks can be made inside D
              and span D (Lemma 38(e): the q(y) lie in D and span it when d = 3; type (F3));
    hyper     W has an invariant hyperplane (d = 3, types (N3) and (F3), Lemma 38(e)).

Each orbit also gets descriptive invariants: the number of matrices of each rank, the dimensions of
the common kernel and of the sum of the images, the number of invariant hyperplanes, whether
span(I, W) is closed under products, whether all products in W vanish, the number of nilpotent
matrices, and the least value of dim(W U) - dim U over non-zero subspaces U of F_2^4 (negative for
a compression space).

Method: the 34 similarity classes of M_4(F_2) (orbits of GL_4(F_2), of order 20160) and their
centralisers by brute force. Every orbit of subspaces contains a subspace that contains a class
representative a; the subspaces containing a lie in the centraliser of a and are built from it.
Each new subspace is swept with all of GL_4(F_2); its images that contain a representative are
marked as seen. Checks, all independent of the sweep:

    - |GL_4(F_2)| = 20160; rank by elimination equals rank by image size for every matrix; every
      inverse; 34 classes, 14 of them invertible (the generating functions prod 1/(1 - 2x^i) and
      prod (1 - x^i)/(1 - 2x^i)), class size times centraliser order = 20160;
    - the number of commuting ordered pairs, sum over classes of size times centraliser size,
      equals Feit and Fine's formula;
    - dimension 1: 32 orbits (the classes other than 0 and I), 65534 subspaces;
    - dimension 2, I allowed: the orbit sizes add up to (commuting pairs - 196606) / 6, the number
      of 2-dimensional commutative subspaces from Feit and Fine;
    - dimension 3, I excluded: the orbit sizes add up to the double count
      sum over representatives a of |class of a| * #{W containing a} / 7, and each divides 20160.

Usage: python m93.py [--minutes 140] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import time
from fractions import Fraction

FULL = 1 << 16
IDENT = 0x8421
GL4 = 20160


def mul(x, y):
    """The product x y of 4 x 4 matrices over F_2; row r of x is bits 4r to 4r + 3, bit c of a
    row is column c."""
    ys = (y & 15, (y >> 4) & 15, (y >> 8) & 15, y >> 12)
    out = 0
    for r in range(4):
        s = (x >> (4 * r)) & 15
        acc = 0
        if s & 1:
            acc ^= ys[0]
        if s & 2:
            acc ^= ys[1]
        if s & 4:
            acc ^= ys[2]
        if s & 8:
            acc ^= ys[3]
        out |= acc << (4 * r)
    return out


def parity(v):
    return bin(v).count("1") & 1


def mat_vec(x, v):
    """x v for a column vector v (bit c is coordinate c)."""
    out = 0
    for r in range(4):
        if parity((x >> (4 * r)) & 15 & v):
            out |= 1 << r
    return out


def vec_mat(f, x):
    """f x for a row vector f (bit r is coordinate r)."""
    acc = 0
    for r in range(4):
        if f >> r & 1:
            acc ^= (x >> (4 * r)) & 15
    return acc


def rank(x):
    rows = [(x >> (4 * r)) & 15 for r in range(4)]
    rk = 0
    for col in range(4):
        piv = next((i for i in range(rk, 4) if rows[i] >> col & 1), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        for i in range(4):
            if i != rk and rows[i] >> col & 1:
                rows[i] ^= rows[rk]
        rk += 1
    return rk


def inverse(x):
    """Gauss-Jordan on [x | I]; None if x is singular."""
    rows = [((x >> (4 * r)) & 15) | (1 << (4 + r)) for r in range(4)]
    for col in range(4):
        piv = next((i for i in range(col, 4) if rows[i] >> col & 1), None)
        if piv is None:
            return None
        rows[col], rows[piv] = rows[piv], rows[col]
        for i in range(4):
            if i != col and rows[i] >> col & 1:
                rows[i] ^= rows[col]
    return sum(((rows[r] >> 4) & 15) << (4 * r) for r in range(4))


def span_of(basis):
    out = [0]
    for b in basis:
        out = out + [v ^ b for v in out]
    return out


def dim_span(vecs):
    s = {0}
    for v in vecs:
        if v not in s:
            s |= {x ^ v for x in s}
    return len(s).bit_length() - 1


def key_of(elems):
    k = 0
    for e in sorted(elems):
        k = (k << 16) | e
    return k


def feit_fine(n, q=2):
    """The number of ordered commuting pairs in M_n(F_q): |GL_n(q)| times the coefficient of x^n
    in prod_(i >= 1) prod_(j >= 0) 1 / (1 - q^(1 - j) x^i) (W. Feit and N. J. Fine, 1960), each
    inner product summed by the q-binomial theorem."""
    poly = [Fraction(0)] * (n + 1)
    poly[0] = Fraction(1)
    for i in range(1, n + 1):
        fac = [Fraction(0)] * (n + 1)
        m = 0
        while i * m <= n:
            den = Fraction(1)
            for ell in range(1, m + 1):
                den *= 1 - Fraction(1, q ** ell)
            fac[i * m] += Fraction(q ** m) / den
            m += 1
        poly = [sum(poly[a] * fac[e - a] for a in range(e + 1)) for e in range(n + 1)]
    gl = 1
    for j in range(n):
        gl *= q ** n - q ** j
    return poly[n] * gl


def subspaces():
    """Every subspace of F_2^4, as frozensets of vectors."""
    seen = {frozenset([0])}
    frontier = [frozenset([0])]
    while frontier:
        nxt = []
        for s in frontier:
            for v in range(1, 16):
                if v not in s:
                    t = frozenset(s | {x ^ v for x in s})
                    if t not in seen:
                        seen.add(t)
                        nxt.append(t)
        frontier = nxt
    return sorted(seen, key=lambda s: (len(s), sorted(s)))


def basis_of(s):
    out, sp = [], {0}
    for v in sorted(s):
        if v not in sp:
            out.append(v)
            sp |= {x ^ v for x in sp}
    return out


SUBSPACE_BASES = [basis_of(s) for s in subspaces() if len(s) > 1]


class Tables:
    """Ranks, GL_4(F_2) with inverses, the similarity classes and their centralisers."""

    def __init__(self):
        self.rank = [rank(x) for x in range(FULL)]
        self.gl = [x for x in range(FULL) if self.rank[x] == 4]
        self.pairs = [(g, inverse(g)) for g in self.gl]
        cls = [-1] * FULL
        self.reps, self.sizes = [], []
        for x in range(FULL):
            if cls[x] >= 0:
                continue
            orb = {mul(mul(g, x), gi) for g, gi in self.pairs}
            for y in orb:
                cls[y] = len(self.reps)
            self.reps.append(x)
            self.sizes.append(len(orb))
        self.cls = cls
        self.cent = {a: [x for x in range(FULL) if mul(a, x) == mul(x, a)] for a in self.reps}
        self.cent_gl = {a: sum(1 for x in self.cent[a] if self.rank[x] == 4) for a in self.reps}

    def checks(self):
        ok = {}
        ok["gl_order"] = len(self.gl) == GL4
        ok["rank_by_image"] = all(len({mat_vec(x, v) for v in range(16)}) == 1 << self.rank[x]
                                  for x in range(FULL))
        ok["inverses"] = all(mul(g, gi) == IDENT == mul(gi, g) for g, gi in self.pairs)
        ok["classes"] = len(self.reps) == 34 and sum(self.sizes) == FULL
        inv = [i for i, a in enumerate(self.reps) if self.rank[a] == 4]
        ok["classes_gl"] = len(inv) == 14 and sum(self.sizes[i] for i in inv) == GL4
        ok["orbit_stabiliser"] = all(self.sizes[i] * self.cent_gl[a] == GL4
                                     for i, a in enumerate(self.reps))
        pairs = sum(self.sizes[i] * len(self.cent[a]) for i, a in enumerate(self.reps))
        ok["feit_fine"] = pairs == feit_fine(4)
        return ok, pairs


def containing_spaces(a, dim, cent, with_identity):
    """Every commutative subspace of dimension dim that contains a (and not I unless allowed),
    keyed by key_of(its elements), with one basis each."""
    found = {}
    if a == 0 or (a == IDENT and not with_identity):
        return found

    def extend(basis, elems, cands):
        if len(basis) == dim:
            k = key_of(elems)
            if k not in found:
                found[k] = tuple(basis)
            return
        es = set(elems)
        last = len(basis) + 1 == dim
        for x in cands:
            if x in es:
                continue
            new = elems + [v ^ x for v in elems]
            if not with_identity and IDENT in new:
                continue
            if last:
                extend(basis + [x], new, ())
            else:
                extend(basis + [x], new, [y for y in cands if mul(x, y) == mul(y, x)])

    extend([a], [0, a], cent)
    return found


def sweep(t, basis, repset, seen):
    """The size of the orbit of span(basis); its images that contain a representative go into
    seen."""
    keys = set()
    for g, gi in t.pairs:
        el = span_of([mul(mul(g, b), gi) for b in basis])
        k = key_of(el)
        if k in keys:
            continue
        keys.add(k)
        if not repset.isdisjoint(el):
            seen.add(k)
    return len(keys)


def run(t, dim, with_identity=False, deadline=None):
    excluded = {0} if with_identity else {0, IDENT}
    reps = [a for a in t.reps if a not in excluded]
    repset = set(reps)
    seen, orbits, containing = set(), [], {}
    complete = True
    for a in reps:
        found = containing_spaces(a, dim, t.cent[a], with_identity)
        containing[a] = len(found)
        for k, basis in sorted(found.items()):
            if k in seen:
                continue
            if deadline is not None and time.time() > deadline:
                complete = False
                break
            orbits.append({"basis": list(basis), "size": sweep(t, basis, repset, seen),
                           "first_class": t.cls[a]})
        if not complete:
            break
    nsub = (1 << dim) - 1
    total = sum(t.sizes[t.cls[a]] * c for a, c in containing.items())
    return {"dim": dim, "with_identity": with_identity, "complete": complete,
            "orbits": orbits, "containing": {str(a): c for a, c in containing.items()},
            "double_count": total, "double_count_ok": total % nsub == 0,
            "subspaces": total // nsub, "orbit_size_sum": sum(o["size"] for o in orbits)}


def picks(nz, kers):
    """Whether one non-zero vector from kers[M] for each M in nz can span dimension 3, i.e. three
    of the M give three independent vectors."""
    for m1, m2, m3 in itertools.combinations(nz, 3):
        for v1 in kers[m1]:
            for v2 in kers[m2]:
                if v2 == v1:
                    continue
                for v3 in kers[m3]:
                    if v3 != v1 and v3 != v2 and v3 != v1 ^ v2:
                        return True
    return False


def flags(t, basis):
    el = span_of(list(basis))
    nz = el[1:]
    rk = [t.rank[x] for x in nz]
    sing = max(rk) < 4
    hyp = [f for f in range(1, 16) if all(vec_mat(f, b) in (0, f) for b in basis)]
    span_i = set(span_of(list(basis) + [IDENT]))
    kers = {x: [v for v in range(1, 16) if mat_vec(x, v) == 0] for x in nz}
    ck = sum(1 for v in range(16) if all(mat_vec(b, v) == 0 for b in basis))
    lk = sum(1 for f in range(16) if all(vec_mat(f, b) == 0 for b in basis))
    return {
        "ranks": [rk.count(r) for r in (1, 2, 3, 4)],
        "singular": sing,
        "common_kernel_dim": ck.bit_length() - 1,
        "image_dim": 4 - (lk.bit_length() - 1),
        "hyperplanes": len(hyp),
        "algebra": all(mul(x, y) in span_i for x in basis for y in basis),
        "square_zero": all(mul(x, y) == 0 for x in basis for y in basis),
        "nilpotent": sum(1 for x in nz if mul(mul(x, x), mul(x, x)) == 0),
        "defect": min(dim_span([mat_vec(b, u) for b in basis for u in ub]) - len(ub)
                      for ub in SUBSPACE_BASES),
        "n4": sing and picks(nz, kers),
        "f3": sing and any(picks(nz, {x: [v for v in kers[x] if not parity(f & v)] for x in nz})
                           for f in hyp),
    }


def categories(orbits):
    tests = {"all": lambda f: True, "singular": lambda f: f["singular"],
             "hyper": lambda f: f["hyperplanes"] > 0,
             "singular_hyper": lambda f: f["singular"] and f["hyperplanes"] > 0,
             "n4": lambda f: f["n4"], "f3": lambda f: f["f3"],
             "singular_not_compression": lambda f: f["singular"] and f["defect"] >= 0}
    return {name: {"orbits": sum(1 for o in orbits if test(o["flags"])),
                   "subspaces": sum(o["size"] for o in orbits if test(o["flags"]))}
            for name, test in tests.items()}


def reps_ok(orbits):
    """Each representative: three independent pairwise commuting matrices, I not in their span,
    and an orbit size dividing 20160."""
    for o in orbits:
        b = o["basis"]
        el = span_of(b)
        if (len(b) != 3 or len(set(el)) != 8 or IDENT in el or GL4 % o["size"]
                or any(mul(x, y) != mul(y, x) for x in b for y in b)):
            return False
    return True


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--minutes", type=float, default=140.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    start = time.time()
    t = Tables()
    graded, pairs = t.checks()
    print(f"tables {round(time.time() - start, 1)} s checks {json.dumps(graded)} pairs {pairs}",
          flush=True)
    d1 = run(t, 1)
    graded["dim1"] = (d1["complete"] and len(d1["orbits"]) == 32 and d1["subspaces"] == FULL - 2
                      == d1["orbit_size_sum"] and d1["double_count_ok"])
    d2 = run(t, 2, with_identity=True)
    want2 = Fraction(pairs - 196606, 6)
    graded["dim2_feit_fine"] = (d2["complete"] and d2["double_count_ok"]
                                and d2["subspaces"] == d2["orbit_size_sum"] == want2)
    print(f"dim1 {len(d1['orbits'])} orbits; dim2 {len(d2['orbits'])} orbits "
          f"{d2['orbit_size_sum']} subspaces (want {want2}) {round(time.time() - start, 1)} s",
          flush=True)
    d3 = run(t, 3, deadline=start + args.minutes * 60)
    graded["dim3_complete"] = d3["complete"]
    graded["dim3_double_count"] = (d3["double_count_ok"]
                                   and d3["subspaces"] == d3["orbit_size_sum"])
    graded["dim3_reps"] = reps_ok(d3["orbits"])
    for o in d3["orbits"]:
        o["flags"] = flags(t, o["basis"])
    cats = categories(d3["orbits"])
    out = {"graded": graded, "commuting_pairs": pairs,
           "classes": [{"rep": a, "size": t.sizes[i], "rank": t.rank[a],
                        "centraliser": len(t.cent[a]), "centraliser_gl": t.cent_gl[a]}
                       for i, a in enumerate(t.reps)],
           "dim1": {k: v for k, v in d1.items() if k != "orbits"} | {"orbits": len(d1["orbits"])},
           "dim2": {k: v for k, v in d2.items() if k not in ("orbits", "containing")}
           | {"orbits": len(d2["orbits"])},
           "dim3": d3, "categories": cats, "seconds": round(time.time() - start, 1)}
    with open(os.path.join(args.out_dir, "m93.json"), "w") as f:
        json.dump(out, f, indent=1)
    print(f"SUMMARY m93 all_match {all(graded.values())} graded {len(graded)} "
          f"dim3_orbits {len(d3['orbits'])} dim3_subspaces {d3['orbit_size_sum']} "
          f"categories {json.dumps(cats, sort_keys=True)} seconds {out['seconds']}", flush=True)


if __name__ == "__main__":
    main()
