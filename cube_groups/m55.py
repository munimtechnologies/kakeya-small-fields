# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m55: how many instances the second-matrix split (the method of Proposition 30, notes/a42.md)
gives for the ten classes of the rank-3 configuration (B5) with d = 3 at t = 7 and dim V = 9
(Proposition 32, notes/a45.md). It counts; it solves nothing.

Coordinates are m42.py's (bit k of a vector is its e_k coordinate): x0 = sigma(u) = e_0,
P = phi(V) = span(e_1, ..., e_5), H0 = P + span(x0) = span(e_0, ..., e_5), and e_6 lies outside
H0. Each class is given by the representative A_u that job m42c or m42d recorded (a t^2-bit mask
with entry (r, c) at bit 7 r + c), with X_1 = ker A_u and R = Im A_u from m46.py's pair tables.

For n in N = ker phi outside span(u), A_n kills x0 and maps H0 into R (Proposition 29 (c)), has
rank at most 2 on X_1 (it kills x0 and sigma(n), independent vectors of X_1), rank at most 3
(Corollary 55), and is neither 0 nor A_u (Corollary 60, d >= 2); A_n e_6 is otherwise free. As
n + u is such an element too, A_n + A_u must also have rank at most 3. These maps form the set
Adm. They are counted up to A -> g A g^(-1) for g in G = {g in GL(X) : g x0 = x0, g P = P,
g A_u = A_u g} and A -> A + A_u (n -> n + u). G is found by solving these linear conditions and
keeping the invertible solutions; the classes by union-find over a generating set of G whose
closure is checked to be all of G.

Graded against counts by hand written before the job ran (Proposition 32): |Adm| (405566 when
X_1 lies in H0, 323966 when it does not) and |G| for each class. The number of classes is
reported, not graded; |Adm| / (2 |G|) bounds it from below.

Usage: python m55.py [--out-dir DIR] [--names NAME,NAME]
"""
import argparse
import json
import os
import random
import time
from array import array

T = 7
X0 = 1
NBITS = 22
ALPHA = (8, 4, 2, 1)     # X_1 = span(e_0, ..., e_3), inside H0 (pair orbits 0 to 19)
BETA = (64, 4, 2, 1)     # X_1 = span(e_0, e_1, e_2, e_6) (pair orbits 20 to 48)
# The ten classes of (B5) with d = 3: representative A_u (from m46.py and m48.py), X_1, R.
CLASSES = {
    "r3b_t7_B5_o000_c000": (266304, ALPHA, (4, 2, 1)),
    "r3b_t7_B5_o000_c001": (266320, ALPHA, (4, 2, 1)),
    "r3b_t7_B5_o000_c002": (270368, ALPHA, (4, 2, 1)),
    "r3b_t7_B5_o001_c000": (34086912, ALPHA, (8, 4, 2)),
    "r3b_t7_B5_o002_c000": (34086976, ALPHA, (8, 4, 3)),
    "r3b_t7_B5_o002_c001": (34089040, ALPHA, (8, 4, 3)),
    "r3b_t7_B5_o020_c000": (133152, BETA, (4, 2, 1)),
    "r3b_t7_B5_o031_c000": (35184372090912, BETA, (64, 2, 1)),
    "r3b_t7_B5_o032_c000": (35184372355072, BETA, (64, 4, 2)),
    "r3b_t7_B5_o033_c000": (35184372355104, BETA, (64, 4, 3)),
}
# Counts by hand (notes/a45.md, Proposition 32), written before the job ran.
HAND_ORDER = {
    "r3b_t7_B5_o000_c000": 24576, "r3b_t7_B5_o000_c001": 8192, "r3b_t7_B5_o000_c002": 8192,
    "r3b_t7_B5_o001_c000": 24576, "r3b_t7_B5_o002_c000": 24576, "r3b_t7_B5_o002_c001": 4096,
    "r3b_t7_B5_o020_c000": 3072, "r3b_t7_B5_o031_c000": 512, "r3b_t7_B5_o032_c000": 1536,
    "r3b_t7_B5_o033_c000": 512,
}
HAND_VALID = {ALPHA: 8 * 344 * 64 + 120 * 1912 - 2, BETA: 344 * 512 + 120 * 1232 - 2}
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


def span_set(vecs):
    s = {0}
    for v in vecs:
        if v not in s:
            s |= {x ^ v for x in s}
    return s


def cols_of(mask):
    """The columns of a matrix given as a t^2-bit mask with entry (r, c) at bit 7 r + c."""
    return tuple(sum(((mask >> (T * r + c)) & 1) << r for r in range(T)) for c in range(T))


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


def entry(j, i):
    """(unknown or None, constant) for entry i of g e_j. Unknowns: x_(5 (j - 1) + (i - 1)) for
    1 <= i, j <= 5 (g P inside P) and x_(25 + i) for g e_6; g e_0 = e_0."""
    if j == 0:
        return None, int(i == 0)
    if j == 6:
        return 25 + i, 0
    if 1 <= i <= 5:
        return 5 * (j - 1) + (i - 1), 0
    return None, 0


def group_conditions(au):
    """Linear conditions on the 32 unknowns for g A_u = A_u g."""
    rows = []
    for j in range(T):
        for k in range(T):
            mask, c = 0, 0
            # entry k of g (A_u e_j)
            for jj in range(T):
                if au[j] >> jj & 1:
                    x, cc = entry(jj, k)
                    if x is not None:
                        mask ^= 1 << x
                    c ^= cc
            # entry k of A_u (g e_j)
            for i in range(T):
                if au[i] >> k & 1:
                    x, cc = entry(j, i)
                    if x is not None:
                        mask ^= 1 << x
                    c ^= cc
            rows.append((mask, c))
    return rows


def g_of(x):
    cols = [X0]
    for j in range(1, 6):
        cols.append(sum(((x >> (5 * (j - 1) + (i - 1))) & 1) << i for i in range(1, 6)))
    cols.append((x >> 25) & 127)
    return tuple(cols)


def group(au):
    sol = solve_affine(group_conditions(au), 32)
    if sol is None:
        raise SystemExit("no solution: the identity should be one")
    part, basis = sol
    if len(basis) > 20:
        raise SystemExit("solution space too large: %d" % len(basis))
    out = []
    x = part
    for i in range(1 << len(basis)):
        if i:
            x ^= basis[(i & -i).bit_length() - 1]
        g = g_of(x)
        if rank(g) == T:
            out.append(g)
    return out, len(basis)


def check_group(au, grp):
    for g in grp:
        if g[0] != X0 or any(g[j] & ~62 for j in range(1, 6)):
            return False
        if compose(g, au) != compose(au, g):
            return False
    return len(set(grp)) == len(grp) and IDENT in set(grp)


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


def structure(au, x1, rb):
    """rank A_u = 3, ker A_u = X_1, Im A_u = R, R inside X_1, and the invariants of the pair."""
    ker = {v for v in range(1 << T) if apply(au, v) == 0}
    img = {apply(au, v) for v in range(1 << T)}
    sx1, sr = span_set(x1), span_set(rb)
    return {"rank_au": rank(au), "ker_is_x1": ker == sx1, "im_is_r": img == sr, "d3": sr <= sx1,
            "x1_in_h0": all(x < 64 for x in x1), "x0_in_r": X0 in sr,
            "r_in_p": all(r & 65 == 0 for r in sr)}


class Maps:
    """The maps A with A x0 = 0 and A(H0) inside R, indexed by 22 bits: bits 3 (j - 1) to
    3 (j - 1) + 2 are the coordinates of A e_j (1 <= j <= 5) in the basis rb of R, and bits 15 to
    21 are A e_6. The encoding is linear, so A -> A + A_u is idx -> idx ^ index(A_u)."""

    def __init__(self, x1, rb):
        assert X0 in x1 and all(bin(x).count("1") == 1 for x in x1)
        self.x1, self.rb = x1, rb
        self.vec = []
        for c in range(8):
            v = 0
            for i in range(3):
                if c >> i & 1:
                    v ^= rb[i]
            self.vec.append(v)
        self.coord = {v: c for c, v in enumerate(self.vec)}
        self.inner = [j for j in range(1, 6) if (1 << j) in x1]
        self.e6_in_x1 = (1 << 6) in x1

    def cols(self, idx):
        return ((0,) + tuple(self.vec[(idx >> (3 * (j - 1))) & 7] for j in range(1, 6))
                + (idx >> 15,))

    def index(self, cols):
        if cols[0] or cols[6] >> 7:
            raise ValueError("not in the space of maps")
        idx = cols[6] << 15
        for j in range(1, 6):
            idx |= self.coord[cols[j]] << (3 * (j - 1))
        return idx

    def rank_x1(self, idx):
        a = self.cols(idx)
        return rank([apply(a, x) for x in self.x1])

    def base_slow(self, idx):
        """rank on X_1 at most 2 and rank at most 3."""
        return self.rank_x1(idx) <= 2 and rank(self.cols(idx)) <= 3

    def base_block(self, h):
        """base_slow(h | v << 15) for v = 0, ..., 127, from the spans of the columns on H0."""
        hc = [self.vec[(h >> (3 * k)) & 7] for k in range(5)]
        sp = span_set(hc)
        rh = rank(hc)
        xin = [hc[j - 1] for j in self.inner]
        rx = rank(xin)
        out = bytearray(128)
        if rx > 2:
            return out
        if self.e6_in_x1:
            spx = span_set(xin)
            for v in range(128):
                out[v] = int(rh + (v not in sp) <= 3 and rx + (v not in spx) <= 2)
        else:
            for v in range(128):
                out[v] = int(rh + (v not in sp) <= 3)
        return out


def base_flags(mp):
    flags = bytearray(1 << NBITS)
    for h in range(1 << 15):
        flags[h::1 << 15] = mp.base_block(h)
    return flags


def conj_index(mp, g, ginv, idx):
    a = mp.cols(idx)
    return mp.index(tuple(apply(g, apply(a, ginv[j])) for j in range(T)))


def index_map(mp, g, ginv):
    """A -> g A g^(-1) is linear in the index: tables for bits 0-7, 8-15 and 16-21."""
    imgs = [conj_index(mp, g, ginv, 1 << k) for k in range(NBITS)]
    tabs = []
    for lo, width in ((0, 8), (8, 8), (16, 6)):
        tab = [0] * (1 << width)
        for x in range(1, 1 << width):
            tab[x] = tab[x & (x - 1)] ^ imgs[lo + (x & -x).bit_length() - 1]
        tabs.append(tab)
    return tabs


def map_apply(tabs, idx):
    return tabs[0][idx & 255] ^ tabs[1][(idx >> 8) & 255] ^ tabs[2][idx >> 16]


def orbits(au_idx, flags, maps):
    vflag = bytearray(1 << NBITS)
    valid = []
    for i in range(1 << NBITS):
        if flags[i] and flags[i ^ au_idx] and i != 0 and i != au_idx:
            vflag[i] = 1
            valid.append(i)
    parent = array("i", range(1 << NBITS))

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

    closed = True
    for i in valid:
        for tabs in maps:
            j = map_apply(tabs, i)
            if not vflag[j]:
                closed = False
            union(i, j)
        union(i, i ^ au_idx)
    orb = {}
    for i in valid:
        orb.setdefault(find(i), []).append(i)
    return valid, orb, closed


def run_class(name, rng, cache):
    t0 = time.time()
    mask, x1, rb = CLASSES[name]
    au = cols_of(mask)
    mp = Maps(x1, rb)
    st = structure(au, x1, rb)
    grp, dim = group(au)
    grp_ok = check_group(au, grp)
    gens = generators(grp, rng)
    if (x1, rb) not in cache:
        cache[(x1, rb)] = base_flags(mp)
    flags = cache[(x1, rb)]
    sample = [rng.randrange(1 << NBITS) for _ in range(3000)]
    fast_ok = all(flags[i] == int(mp.base_slow(i)) for i in sample)
    au_idx = mp.index(au)
    pairs = [(g, inverse(g)) for g in gens]
    maps = [index_map(mp, g, gi) for g, gi in pairs]
    linear_ok = all(map_apply(tabs, i) == conj_index(mp, g, gi, i)
                    for (g, gi), tabs in zip(pairs, maps) for i in sample[:300])
    valid, orb, closed = orbits(au_idx, flags, maps)
    by_rank, reps, sizes_ok = {}, [], True
    for root, members in sorted(orb.items()):
        rk = mp.rank_x1(root)
        if any(mp.rank_x1(i) != rk for i in members):
            sizes_ok = False
        if (2 * len(grp)) % len(members):
            sizes_ok = False
        by_rank[rk] = by_rank.get(rk, 0) + 1
        reps.append({"index": root, "cols": list(mp.cols(root)), "rank_x1": rk,
                     "rank": rank(mp.cols(root)), "size": len(members)})
    sizes_ok = sizes_ok and sum(r["size"] for r in reps) == len(valid)
    return {
        "name": name, "au": mask, "x1": list(x1), "r": list(rb),
        "structure": st,
        "solution_space_dim": dim,
        "order": len(grp), "order_hand": HAND_ORDER[name], "group_checked": grp_ok,
        "generators": len(gens),
        "valid": len(valid), "valid_hand": HAND_VALID[x1],
        "fast_matches_slow": fast_ok, "linear_ok": linear_ok, "action_closed": closed,
        "orbits": len(orb), "lower_bound": -(-len(valid) // (2 * len(grp))),
        "orbits_by_rank_x1": {str(k): v for k, v in sorted(by_rank.items())},
        "sizes_ok": sizes_ok,
        "reps": reps,
        "seconds": round(time.time() - t0, 1),
    }


def grade(results):
    checks = {}
    for name, r in results.items():
        s = r["structure"]
        tag = name[10:]
        checks["structure_" + tag] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["im_is_r"]
                                      and s["d3"] and s["x1_in_h0"] == (tuple(r["x1"]) == ALPHA))
        checks["group_" + tag] = r["group_checked"] and r["order"] == r["order_hand"]
        checks["valid_" + tag] = (r["valid"] == r["valid_hand"] and r["action_closed"]
                                  and r["fast_matches_slow"] and r["linear_ok"])
        checks["sizes_" + tag] = r["sizes_ok"]
    return {"checks": checks, "passed": sum(checks.values()), "total": len(checks),
            "all_held": all(checks.values()),
            "orbits": {k[10:]: r["orbits"] for k, r in results.items()},
            "lower_bounds": {k[10:]: r["lower_bound"] for k, r in results.items()},
            "orders": {k[10:]: r["order"] for k, r in results.items()},
            "valid": {k[10:]: r["valid"] for k, r in results.items()}}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--names", default=",".join(CLASSES))
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    rng = random.Random(55)
    results, cache = {}, {}
    for name in args.names.split(","):
        results[name] = r = run_class(name, rng, cache)
        print(name, "order", r["order"], "valid", r["valid"], "orbits", r["orbits"],
              r["orbits_by_rank_x1"], "%.1f s" % r["seconds"], flush=True)
        with open(os.path.join(args.out_dir, "m55_%s.json" % name[10:]), "w") as f:
            json.dump(r, f, indent=1)
    g = grade(results)
    with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
        json.dump(g, f, indent=1)
    print("SUMMARY", json.dumps({k: v for k, v in g.items() if k != "checks"}), flush=True)
    print("SUMMARY checks %d of %d held" % (g["passed"], g["total"]), flush=True)


if __name__ == "__main__":
    main()
