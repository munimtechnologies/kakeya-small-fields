# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m66: a machine check of Proposition 33 (notes/a52.md), the second-matrix split of the 51
classes of (B6) with d = dim(X_1 n R) <= 2 that were open on 2026-10-21, at t = 7 and dim V = 9.

m42's coordinates (bit k of a vector is its e_k coordinate): X = F_2^7, x0 = e_0,
P = span(e_1, ..., e_6), X_1 = ker A_u = span(e_0, ..., e_3), R = Im A_u. A matrix is an int with
entry (r, c) at bit 7r + c (m42's masks); here it is also a tuple of 7 columns.

G is the group of g in GL(X) with g x0 = x0, g P = P and g A_u = A_u g. As in m52.py it is found by
solving these linear conditions over F_2 and keeping the invertible solutions, not from the
parametrisation of Proposition 33 (b). The maps counted are Adm of Proposition 33 (a): A x0 = 0,
image in R, rank on X_1 at most 2, and, when d >= 1, A != 0 and A != A_u. They are counted up to
A -> g A g^(-1) (g in G) and A -> A + A_u (n -> n + u), by union-find over a generating set of G
whose closure is checked to be all of G. Conjugation is linear in A, so each generator acts on the
18-bit index of A through three 64-entry tables.

The class lists (m42b's representatives) are m58.py's, imported unchanged. The orbit roots are the
smallest index in each orbit, so the representatives do not depend on the generators chosen.

Parts:
    count   for each class (or --names): G, Adm, the orbits by rank on X_1, with the roots and
            sizes, to out/m66_<name>.json; a summary to out/count.json.
    grade   graded: structure of A_u (kernel X_1, image R of its pair, rank 3, d by hand), G checked
            element by element, |G| against Proposition 33 (c), |Adm| against (a), Adm closed under
            G, orbit sizes dividing 2 |G| and adding up to |Adm|, and the 7 exact counts of (d).
            Reported, not graded: the orbit counts for d >= 1 and their ratio to the lower bound.

Usage: python m66.py --part count|grade [--names N1,N2] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time

import m58

T = 7
X0 = 1
P_BITS = 0b1111110
X1B = (1, 2, 4, 8)
IDENT = tuple(1 << j for j in range(T))
DIM_CAP = 22

# Proposition 33 (c) and (d) (notes/a52.md), by hand, written before this job ran.
HAND_ORDER = {
    "r3b_t7_B6_o003_c000": 1536, "r3b_t7_B6_o003_c001": 1536, "r3b_t7_B6_o003_c002": 3072,
    "r3b_t7_B6_o003_c003": 3072, "r3b_t7_B6_o003_c004": 3072,
    "r3b_t7_B6_o004_c000": 1536, "r3b_t7_B6_o004_c001": 2048,
    "r3b_t7_B6_o005_c000": 512, "r3b_t7_B6_o005_c001": 512, "r3b_t7_B6_o005_c002": 1024,
    "r3b_t7_B6_o005_c003": 512,
    "r3b_t7_B6_o006_c000": 1536, "r3b_t7_B6_o006_c001": 2048,
    "r3b_t7_B6_o007_c001": 1344, "r3b_t7_B6_o007_c002": 2688, "r3b_t7_B6_o007_c003": 4032,
    "r3b_t7_B6_o007_c004": 1344, "r3b_t7_B6_o007_c006": 1344, "r3b_t7_B6_o007_c007": 1344,
    "r3b_t7_B6_o007_c009": 2688,
    "r3b_t7_B6_o008_c000": 384, "r3b_t7_B6_o008_c001": 576, "r3b_t7_B6_o008_c002": 768,
    "r3b_t7_B6_o008_c003": 384, "r3b_t7_B6_o008_c004": 1152,
    "r3b_t7_B6_o009_c000": 384, "r3b_t7_B6_o009_c001": 192, "r3b_t7_B6_o009_c002": 384,
    "r3b_t7_B6_o009_c003": 576, "r3b_t7_B6_o009_c004": 192, "r3b_t7_B6_o009_c005": 192,
    "r3b_t7_B6_o009_c006": 192, "r3b_t7_B6_o009_c007": 192, "r3b_t7_B6_o009_c008": 1152,
    "r3b_t7_B6_o009_c009": 384,
    "r3b_t7_B6_o010_c000": 192, "r3b_t7_B6_o010_c001": 192, "r3b_t7_B6_o010_c002": 768,
    "r3b_t7_B6_o010_c003": 384, "r3b_t7_B6_o010_c004": 384, "r3b_t7_B6_o010_c005": 384,
    "r3b_t7_B6_o010_c006": 384, "r3b_t7_B6_o010_c007": 384, "r3b_t7_B6_o010_c008": 384,
    "r3b_t7_B6_o011_c002": 672, "r3b_t7_B6_o011_c003": 1176, "r3b_t7_B6_o011_c004": 1176,
    "r3b_t7_B6_o012_c001": 168, "r3b_t7_B6_o012_c004": 336, "r3b_t7_B6_o012_c009": 504,
    "r3b_t7_B6_o012_c011": 1344,
}
HAND_ORBITS_D0 = {
    "r3b_t7_B6_o011_c002": 994, "r3b_t7_B6_o011_c003": 552, "r3b_t7_B6_o011_c004": 552,
    "r3b_t7_B6_o012_c001": 3840, "r3b_t7_B6_o012_c004": 1976, "r3b_t7_B6_o012_c009": 1288,
    "r3b_t7_B6_o012_c011": 553,
}
HAND_ADM = {0: 344 * 512, 1: 344 * 512 - 2, 2: 344 * 512 - 2}


def classes():
    """{name: A_u mask} for the 51 classes: m58's two lists."""
    out = dict(m58.OPEN_M45)
    out.update(m58.OPEN_M47)
    return out


def pair_of(name):
    return int(name.split("_o")[1][:3])


# ---------- F_2 linear algebra on bitmasks ----------

def cols_of_mask(mask):
    """Column c of an m42 mask (entry (r, c) at bit 7r + c) as a vector bitmask."""
    return tuple(sum(((mask >> (T * r + c)) & 1) << r for r in range(T)) for c in range(T))


def apply(m, v):
    r, j = 0, 0
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


def span(vecs):
    out = {0}
    for v in vecs:
        out |= {w ^ v for w in out}
    return out


def solve_affine(rows, n):
    """As m52.solve_affine: rows (mask, c) mean sum of x_i over mask = c over F_2, n unknowns.
    Returns (particular solution, basis of the homogeneous solutions), or None."""
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


# ---------- the group G ----------

def group_conditions(au):
    """Unknown x_(6(j - 1) + (i - 1)) = coefficient of e_i in g e_j, for 1 <= i, j <= 6 (g e_j lies in
    P); g e_0 = e_0. Rows: component k of g(A_u e_j) + A_u(g e_j) = 0 for every j and k."""
    rows = []
    for j in range(1, T):
        v = au[j]
        for k in range(T):
            mask, c = 0, 0
            for jj in range(T):
                if v >> jj & 1:
                    if jj == 0:
                        c ^= int(k == 0)
                    elif k >= 1:
                        mask ^= 1 << (6 * (jj - 1) + (k - 1))
            for i in range(1, T):
                if au[i] >> k & 1:
                    mask ^= 1 << (6 * (j - 1) + (i - 1))
            rows.append((mask, c))
    # j = 0: A_u e_0 = 0 and g e_0 = e_0, so both sides vanish.
    return rows


def group(au):
    sol = solve_affine(group_conditions(au), 36)
    if sol is None:
        return [], -1
    part, basis = sol
    if len(basis) > DIM_CAP:
        return [], len(basis)
    out = []
    x = part
    for i in range(1 << len(basis)):
        if i:
            x ^= basis[(i & -i).bit_length() - 1]
        cols = (X0,) + tuple(((x >> (6 * (j - 1))) & 63) << 1 for j in range(1, T))
        if rank(cols) == T:
            out.append(cols)
    return out, len(basis)


def check_group(au, grp):
    for g in grp:
        if g[0] != X0 or any(g[j] & ~P_BITS for j in range(1, T)) or rank(g) != T:
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


# ---------- the maps ----------

class Maps:
    """The maps A with A x0 = 0 and image in R = span(r_0, r_1, r_2), indexed by 18 bits: bits
    3(j - 1) to 3(j - 1) + 2 are the coordinates of A e_j (1 <= j <= 6) in the basis r_0, r_1, r_2."""

    def __init__(self, rb):
        self.rb = tuple(rb)
        self.vec = [apply(self.rb, c) for c in range(8)]
        self.coord = {v: c for c, v in enumerate(self.vec)}
        self.rank9 = [rank([self.vec[(i >> (3 * k)) & 7] for k in range(3)]) for i in range(512)]

    def cols(self, idx):
        return (0,) + tuple(self.vec[(idx >> (3 * (j - 1))) & 7] for j in range(1, T))

    def index(self, cols):
        if cols[0]:
            raise ValueError("A x0 != 0")
        return sum(self.coord[cols[j]] << (3 * (j - 1)) for j in range(1, T))

    def rank_x1(self, idx):
        """Columns 1 to 3 are the low 9 bits; column 0 is 0."""
        return self.rank9[idx & 511]

    def conj_direct(self, g, ginv, idx):
        a = self.cols(idx)
        return self.index(tuple(apply(g, apply(a, ginv[j])) for j in range(T)))

    def conj_tables(self, g):
        """A -> g A g^(-1) is linear in A: three 64-entry tables on the 6-bit chunks of the index."""
        ginv = inverse(g)
        img = [self.conj_direct(g, ginv, 1 << b) for b in range(18)]
        tabs = []
        for chunk in range(3):
            tab = [0] * 64
            for i in range(1, 64):
                low = (i & -i).bit_length() - 1
                tab[i] = tab[i & (i - 1)] ^ img[6 * chunk + low]
            tabs.append(tab)
        return tabs


def structure(name, au_mask):
    au = cols_of_mask(au_mask)
    pair = pair_of(name)
    rb = m58.B6_PAIR_R[pair]
    ker = {v for v in range(1 << T) if apply(au, v) == 0}
    img = {apply(au, v) for v in range(1 << T)}
    dim_sum = rank(list(X1B) + list(rb))
    return {"rank_au": rank(au), "ker_is_x1": ker == span(X1B), "image_is_r": img == span(rb),
            "d": len(X1B) + len(rb) - dim_sum, "d_hand": m58.HAND_D_PAIR[pair]}


def count_class(name, au_mask, rng):
    t0 = time.time()
    au = cols_of_mask(au_mask)
    st = structure(name, au_mask)
    d = st["d_hand"]
    rb = m58.B6_PAIR_R[pair_of(name)]
    mp = Maps(rb)
    grp, dim = group(au)
    out = {"name": name, "structure": st, "solution_space_dim": dim, "order": len(grp),
           "order_hand": HAND_ORDER.get(name)}
    if not grp:
        out["error"] = "no group (dimension %d)" % dim
        return out
    out["group_checked"] = check_group(au, grp)
    gens = generators(grp, rng)
    au_idx = mp.index(au)
    n = 1 << 18
    valid = [i for i in range(n) if mp.rank_x1(i) <= 2 and (d == 0 or i not in (0, au_idx))]
    vset = bytearray(n)
    for i in valid:
        vset[i] = 1
    parent = list(range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    closed = True
    tabs = [mp.conj_tables(g) for g in gens]
    for i in valid:
        a, b, c = i & 63, (i >> 6) & 63, i >> 12
        for t0_, t1_, t2_ in tabs:
            j = t0_[a] ^ t1_[b] ^ t2_[c]
            if not vset[j]:
                closed = False
                continue
            ri, rj = find(i), find(j)
            if ri != rj:
                parent[max(ri, rj)] = min(ri, rj)
        ri, rj = find(i), find(i ^ au_idx)
        if ri != rj:
            parent[max(ri, rj)] = min(ri, rj)
    size, rk_bad = {}, False
    for i in valid:
        r = find(i)
        size[r] = size.get(r, 0) + 1
        if mp.rank_x1(i) != mp.rank_x1(r):
            rk_bad = True
    by_rank = {}
    for r in size:
        k = str(mp.rank_x1(r))
        by_rank[k] = by_rank.get(k, 0) + 1
    # Spot-check the tables against direct conjugation.
    g0 = gens[0]
    gi0 = inverse(g0)
    spot = all(mp.conj_direct(g0, gi0, i) == (tabs[0][0][i & 63] ^ tabs[0][1][(i >> 6) & 63]
                                              ^ tabs[0][2][i >> 12])
               for i in rng.sample(valid, 200))
    out.update({
        "d": d, "au_index": au_idx, "generators": len(gens), "valid": len(valid),
        "valid_hand": HAND_ADM[d], "action_closed": closed, "tables_match": spot,
        "orbits": len(size), "orbits_by_rank_x1": dict(sorted(by_rank.items())),
        "orbits_hand": HAND_ORBITS_D0.get(name),
        "lower_bound": -(-len(valid) // (2 * len(grp))),
        "sizes_ok": (not rk_bad and sum(size.values()) == len(valid)
                     and all((2 * len(grp)) % s == 0 for s in size.values())),
        "reps": [[r, mp.rank_x1(r), s] for r, s in sorted(size.items())],
        "seconds": round(time.time() - t0, 1),
    })
    return out


def run_count(names, out_dir):
    rng = random.Random(66)
    cl = classes()
    summary = {}
    for name in names:
        r = count_class(name, cl[name], rng)
        with open(os.path.join(out_dir, "m66_%s.json" % name), "w") as f:
            json.dump(r, f)
        summary[name] = {k: v for k, v in r.items() if k != "reps"}
        print(name, "order", r.get("order"), "valid", r.get("valid"), "orbits", r.get("orbits"),
              r.get("orbits_by_rank_x1"), "%s s" % r.get("seconds"), flush=True)
    with open(os.path.join(out_dir, "count.json"), "w") as f:
        json.dump(summary, f, indent=1)


# ---------- grading (pre-registered in m66-predictions.md) ----------

def grade(out_dir, names):
    graded, ungraded, report = {}, {}, {}
    try:
        with open(os.path.join(out_dir, "count.json")) as f:
            summary = json.load(f)
    except (OSError, ValueError):
        summary = {}
    graded["list"] = (len(classes()) == 51 and set(HAND_ORDER) == set(classes())
                      and set(HAND_ORBITS_D0) <= set(HAND_ORDER))
    totals = {}
    for name in names:
        r = summary.get(name)
        if r is None or "error" in r:
            ungraded[name] = "missing" if r is None else r["error"]
            continue
        s = r["structure"]
        graded["structure_" + name] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["image_is_r"]
                                       and s["d"] == s["d_hand"])
        graded["group_" + name] = r["group_checked"] and r["order"] == r["order_hand"]
        graded["adm_" + name] = (r["valid"] == r["valid_hand"] and r["action_closed"]
                                 and r["tables_match"])
        graded["sizes_" + name] = r["sizes_ok"]
        if r["orbits_hand"] is not None:
            graded["orbits_" + name] = r["orbits"] == r["orbits_hand"]
        t = totals.setdefault(str(r["d"]), {"classes": 0, "orbits": 0, "bound": 0, "rank0": 0})
        t["classes"] += 1
        t["orbits"] += r["orbits"]
        t["bound"] += r["lower_bound"]
        t["rank0"] += r["orbits_by_rank_x1"].get("0", 0)
        report[name] = [r["orbits"], r["orbits_by_rank_x1"], r["lower_bound"],
                        round(r["orbits"] / r["lower_bound"], 2)]
    for t in totals.values():
        t["ratio"] = round(t["orbits"] / t["bound"], 2) if t["bound"] else None
    return {"graded": graded, "ungraded": ungraded, "all_held": all(graded.values()) and not
            ungraded, "totals_by_d": totals, "per_class": report,
            "total_orbits": sum(t["orbits"] for t in totals.values())}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["count", "grade"], default="count")
    ap.add_argument("--names", default="")
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    names = args.names.split(",") if args.names else sorted(classes())
    if args.part == "count":
        run_count(names, args.out_dir)
    else:
        out = grade(args.out_dir, names)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(f"SUMMARY grade all_held {out['all_held']} graded {len(out['graded'])} "
              f"failed {sum(not v for v in out['graded'].values())} "
              f"ungraded {len(out['ungraded'])} total_orbits {out['total_orbits']} "
              f"totals {json.dumps(out['totals_by_d'], sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
