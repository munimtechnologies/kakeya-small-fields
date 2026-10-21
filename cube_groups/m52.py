# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m52: a machine check of Proposition 30 (notes/a42.md), the class count by hand for the
second-matrix split of the three classes of (B6) with d = 3 at t = 7 and dim V = 9.

In adapted coordinates (bit k of a vector is its e_k coordinate): X = F_2^7, x0 = e_6,
P = span(e_0, ..., e_5), and A_u sends e_3, e_4, e_5 to a basis r_0, r_1, r_2 of R and kills
e_0, e_1, e_2, e_6, so X_1 = ker A_u = span(e_0, e_1, e_2, e_6) contains R (d = 3):

    kind P      R = span(e_0, e_1, e_2)          (R inside P)
    kind graph  R = span(e_0, e_1, e_2 + e_6)    (x0 not in R, R not inside P)
    kind L      R = span(e_0, e_1, e_6)          (x0 in R)

By Lemma 82's argument (notes/a36.md) each kind is a single class of A_u in (B6), so these are
the three classes with d = 3 up to base change.

G is the group of g in GL(X) with g x0 = x0, g P = P and g A_u = A_u g. It is found here by
solving these linear conditions over F_2 and keeping the invertible solutions, not from the
parametrisation in a42.md. The maps counted are the possible A_n for n in ker phi outside
span(u) (Proposition 30 (a)): A x0 = 0, image in R, rank of A on X_1 at most 2, A not 0 and not
A_u. They are counted up to A -> g A g^(-1) (g in G) and A -> A + A_u (n -> n + u), by union-find
over a generating set of G whose closure is checked to be all of G.

Usage: python m52.py [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time

T = 7
X0 = 1 << 6
X1B = (1 << 0, 1 << 1, 1 << 2, 1 << 6)
KINDS = {
    "P": (1 << 0, 1 << 1, 1 << 2),
    "graph": (1 << 0, 1 << 1, (1 << 2) | (1 << 6)),
    "L": (1 << 0, 1 << 1, 1 << 6),
}
# Counts by hand (notes/a42.md, Proposition 30), written before the job ran. None: not counted
# by hand. HAND_ORBITS is keyed by the rank of A on X_1.
HAND_ORDER = {"P": 86016, "graph": 12288, "L": 12288}
HAND_ORBITS = {"P": {0: 6, 1: 20, 2: 14}, "graph": {0: 18, 1: 94, 2: 66}, "L": None}
HAND_VALID = 344 * 512 - 2
IDENT = tuple(1 << j for j in range(T))


def apply(m, v):
    """m is a tuple of T columns (bitmasks); returns the vector m v."""
    r = 0
    j = 0
    while v:
        if v & 1:
            r ^= m[j]
        v >>= 1
        j += 1
    return r


def compose(a, b):
    """The matrix a b (apply b first)."""
    return tuple(apply(a, c) for c in b)


def rank(vecs):
    piv = {}
    for v in vecs:
        while v:
            h = v.bit_length() - 1
            if h in piv:
                v ^= piv[h]
            else:
                piv[h] = v
                break
    return len(piv)


def inverse(g):
    tab = [0] * (1 << T)
    for v in range(1 << T):
        tab[apply(g, v)] = v
    return tuple(tab[1 << j] for j in range(T))


def au_of(kind):
    rb = KINDS[kind]
    return (0, 0, 0, rb[0], rb[1], rb[2], 0)


def solve_affine(rows, n):
    """rows: (mask, c) meaning the sum of x_i over the bits of mask is c, over F_2, n unknowns.
    Returns (particular solution, basis of the solutions of the homogeneous system), or None."""
    piv = {}
    for mask, c in rows:
        for b, (pm, pc) in piv.items():
            if mask >> b & 1:
                mask ^= pm
                c ^= pc
        if mask:
            b = mask.bit_length() - 1
            for bb in list(piv):
                pm, pc = piv[bb]
                if pm >> b & 1:
                    piv[bb] = (pm ^ mask, pc ^ c)
            piv[b] = (mask, c)
        elif c:
            return None
    part = 0
    for b, (m, c) in piv.items():
        if c:
            part |= 1 << b
    basis = []
    for f in range(n):
        if f in piv:
            continue
        v = 1 << f
        for b, (m, c) in piv.items():
            if m >> f & 1:
                v |= 1 << b
        basis.append(v)
    return part, basis


def group_conditions(au):
    """Linear conditions on g restricted to P (unknown x_(6j + i) = entry i of g e_j, i, j < 6;
    g e_j has no e_6 part and g e_6 = e_6) for g A_u = A_u g."""
    rows = []
    for j in range(T):
        v = au[j]
        for k in range(T):
            mask, c = 0, 0
            # component k of g(A_u e_j)
            for jj in range(T):
                if v >> jj & 1:
                    if jj == 6:
                        c ^= int(k == 6)
                    elif k < 6:
                        mask ^= 1 << (6 * jj + k)
            # component k of A_u(g e_j); A_u e_6 = 0
            if j < 6:
                for i in range(6):
                    if au[i] >> k & 1:
                        mask ^= 1 << (6 * j + i)
            rows.append((mask, c))
    return rows


def group(kind):
    au = au_of(kind)
    sol = solve_affine(group_conditions(au), 36)
    assert sol is not None
    part, basis = sol
    if len(basis) > 20:
        raise SystemExit("solution space too large: %d" % len(basis))
    out = []
    x = part
    for i in range(1 << len(basis)):
        if i:
            x ^= basis[(i & -i).bit_length() - 1]
        cols = tuple((x >> (6 * j)) & 63 for j in range(6)) + (X0,)
        if rank(cols) == T:
            out.append(cols)
    return out, len(basis)


def check_group(kind, grp):
    au = au_of(kind)
    for g in grp:
        if apply(g, X0) != X0 or any(g[j] >> 6 & 1 for j in range(6)):
            return False
        if compose(g, au) != compose(au, g):
            return False
    return len(set(grp)) == len(grp)


def closure_size(gens):
    seen = {IDENT}
    todo = [IDENT]
    while todo:
        h = todo.pop()
        for g in gens:
            k = compose(g, h)
            if k not in seen:
                seen.add(k)
                todo.append(k)
    return len(seen)


def generators(grp, rng):
    gens = [rng.choice(grp), rng.choice(grp)]
    while closure_size(gens) < len(grp):
        gens.append(rng.choice(grp))
    return gens


def structure(kind):
    """Sanity facts about the class: rank A_u = 3, ker A_u = X_1, R inside X_1, x0 not in P,
    and the kind."""
    au = au_of(kind)
    rb = KINDS[kind]
    ker = [v for v in range(1 << T) if apply(au, v) == 0]
    # the projection onto span(e_0, e_1, e_2, e_6) has image X_1
    span_x1 = {apply(tuple(X1B[:3]) + (0, 0, 0, X1B[3]), v) for v in range(1 << T)}
    span_r = {apply(rb + (0,) * 4, v) for v in range(8)}
    r_in_p = all(not (r >> 6 & 1) for r in rb)
    x0_in_r = X0 in span_r
    want = {"P": (True, False), "graph": (False, False), "L": (False, True)}[kind]
    return {"rank_au": rank(au), "ker_is_x1": set(ker) == span_x1,
            "r_in_x1": span_r <= span_x1, "kind_ok": (r_in_p, x0_in_r) == want}


class Maps:
    """The maps A with A x0 = 0 and image in R, indexed by 18 bits: bits 3j to 3j + 2 are the
    coordinates of A e_j (j < 6) in the basis r_0, r_1, r_2."""

    def __init__(self, kind):
        self.rb = KINDS[kind]
        self.vec = []
        for c in range(8):
            v = 0
            for i in range(3):
                if c >> i & 1:
                    v ^= self.rb[i]
            self.vec.append(v)
        self.coord = {v: c for c, v in enumerate(self.vec)}
        self.au_idx = (1 << 9) | (2 << 12) | (4 << 15)

    def cols(self, idx):
        return tuple(self.vec[(idx >> (3 * j)) & 7] for j in range(6)) + (0,)

    def index(self, cols):
        assert cols[6] == 0
        return sum(self.coord[cols[j]] << (3 * j) for j in range(6))

    def rank_x1(self, idx):
        a = self.cols(idx)
        return rank([apply(a, x) for x in X1B])

    def valid(self, idx):
        return idx != 0 and idx != self.au_idx and self.rank_x1(idx) <= 2

    def conj(self, g, ginv, idx):
        a = self.cols(idx)
        return self.index(tuple(apply(g, apply(a, ginv[j])) for j in range(T)))


def orbits(kind, gens):
    mp = Maps(kind)
    n = 1 << 18
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def union(i, j):
        i, j = find(i), find(j)
        if i != j:
            if i < j:
                parent[j] = i
            else:
                parent[i] = j

    pairs = [(g, inverse(g)) for g in gens]
    valid = [i for i in range(n) if mp.valid(i)]
    ok_closed = True
    for i in valid:
        for g, gi in pairs:
            j = mp.conj(g, gi, i)
            if not mp.valid(j):
                ok_closed = False
            union(i, j)
        union(i, i ^ mp.au_idx)
    orb = {}
    for i in valid:
        orb.setdefault(find(i), []).append(i)
    return mp, valid, orb, ok_closed


def run_kind(kind, rng):
    t0 = time.time()
    grp, dim = group(kind)
    grp_ok = check_group(kind, grp)
    gens = generators(grp, rng)
    mp, valid, orb, closed = orbits(kind, gens)
    by_rank = {}
    reps = []
    sizes_ok = True
    for root, members in sorted(orb.items()):
        rk = mp.rank_x1(root)
        if any(mp.rank_x1(i) != rk for i in members):
            sizes_ok = False
        if (2 * len(grp)) % len(members):
            sizes_ok = False
        by_rank[rk] = by_rank.get(rk, 0) + 1
        a = mp.cols(root)
        reps.append({"index": root, "cols": list(a), "rank_x1": rk, "rank": rank(a),
                     "size": len(members)})
    hand = HAND_ORBITS[kind]
    return {
        "kind": kind,
        "structure": structure(kind),
        "solution_space_dim": dim,
        "order": len(grp),
        "order_hand": HAND_ORDER[kind],
        "group_checked": grp_ok,
        "generators": len(gens),
        "valid": len(valid),
        "valid_hand": HAND_VALID,
        "action_closed": closed,
        "orbits": len(orb),
        "orbits_by_rank_x1": {str(k): v for k, v in sorted(by_rank.items())},
        "orbits_hand": None if hand is None else sum(hand.values()),
        "orbits_by_rank_x1_hand": None if hand is None else {str(k): v for k, v in
                                                              sorted(hand.items())},
        "sizes_ok": sizes_ok and sum(r["size"] for r in reps) == len(valid),
        "reps": reps,
        "seconds": round(time.time() - t0, 1),
    }


def grade(results):
    checks = {}
    for kind, r in results.items():
        s = r["structure"]
        checks["structure_" + kind] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["r_in_x1"]
                                       and s["kind_ok"])
        checks["group_" + kind] = r["group_checked"] and r["order"] == r["order_hand"]
        checks["valid_" + kind] = r["valid"] == r["valid_hand"] and r["action_closed"]
        checks["sizes_" + kind] = r["sizes_ok"]
        if r["orbits_hand"] is not None:
            checks["orbits_" + kind] = (r["orbits"] == r["orbits_hand"] and
                                        r["orbits_by_rank_x1"] == r["orbits_by_rank_x1_hand"])
    return {"checks": checks, "passed": sum(checks.values()), "total": len(checks),
            "all_held": all(checks.values()),
            "orbits": {k: r["orbits"] for k, r in results.items()},
            "orbits_by_rank_x1": {k: r["orbits_by_rank_x1"] for k, r in results.items()}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--kinds", default="P,graph,L")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng = random.Random(52)
    results = {}
    for kind in args.kinds.split(","):
        results[kind] = run_kind(kind, rng)
        r = results[kind]
        print(kind, "order", r["order"], "valid", r["valid"], "orbits", r["orbits"],
              r["orbits_by_rank_x1"], "%.1f s" % r["seconds"], flush=True)
        with open(os.path.join(args.out_dir, "m52_%s.json" % kind), "w") as f:
            json.dump(r, f, indent=1)
    g = grade(results)
    with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
        json.dump(g, f, indent=1)
    print(json.dumps({k: v for k, v in g.items() if k != "orbits_by_rank_x1"}))


if __name__ == "__main__":
    main()
