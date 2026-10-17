# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Lemma 29, Proposition 23, Theorem 25 and Corollary 16 of finite-groups.md (section 14, version
1.7.9): irreducible spaces of matrices of rank <= 2, A(4) <= 5, A(5) <= 7, and the settled cases.

Setting as in m4_irred.py. A subspace C of M_t(F_2) is *irreducible* if no subspace Y with
0 < dim Y < t has A Y <= Y for every A in C. Lemma 29: for t >= 4, an irreducible C whose elements
all have rank <= 2 has a hyperplane P and a vector q outside P with A P <= span(q) for every A in C
(the form of Lemma 28). The proof uses Theorem 3.5 of C. de Seguins Pazzis (arXiv 1405.1575): for
n, p >= 3, a subspace of M_(n,p)(F_2) of upper rank 2 is equivalent to a subspace of R(2,0),
R(0,2) or R(1,1), or to a zero-padded primitive subspace of M_3(F_2). For t >= 4 this says that
every such C is *covered*: its elements share a non-zero kernel vector, or their images span a
space of dimension <= 2, or there are a hyperplane P and a vector q with A P <= span(q) for every A.

Parts. cases: the bounds of Proposition 23 for A(t) and M(t) - t, and the table of settled (a, b)
(Corollary 16). rank2: random spaces of matrices of rank <= 2 in M_t(F_2), t = 3, 4, 5, grown
greedily (from 0 and, for t >= 4, from zero-padded copies of the primitive spaces of M_3(F_2));
for t = 4 and 5 every one and every initial part of one must be covered, and every irreducible one
must have the form of Lemma 28. pairs: every 2-dimensional space of matrices of rank <= 2 in
M_4(F_2), up to equivalence, is covered. control: the primitive spaces A_3, U_3, V_3 and J_3 of
M_3(F_2), as transcribed from that paper, have upper rank 2 and are not covered.

Vectors of F_2^t are int bitmasks (coordinate i at bit i); a t x t matrix is a t^2-bit mask with
entry (r, c) at bit t r + c (0-based), so (A x)_r = parity(row r of A & x). Pure Python, no
dependencies; the helpers are copied from m4_irred.py so that this file runs on its own.

Usage: python m5_rank2.py [--out-dir DIR] [--part cases|rank2|pairs|control]
                          [--budget-minutes 20]
"""
import argparse
import itertools
import json
import os
import random
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


def subspaces(nbits, c):
    """Every c-dimensional subspace of F_2^nbits, once each, as its reduced echelon basis."""
    for piv in itertools.combinations(range(nbits), c):
        pset = set(piv)
        frees = [[j for j in range(p) if j not in pset] for p in piv]
        for choice in itertools.product(*[range(1 << len(f)) for f in frees]):
            rows = []
            for p, f, x in zip(piv, frees, choice):
                row = 1 << p
                for t, j in enumerate(f):
                    if (x >> t) & 1:
                        row |= 1 << j
                rows.append(row)
            yield rows


def elements(basis):
    """Every element of the span of basis (with repeats if basis is dependent)."""
    out = [0]
    for b in basis:
        out += [b ^ e for e in out]
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


def columns_of(A, t):
    return [sum(((A >> (t * r + c)) & 1) << r for r in range(t)) for c in range(t)]


def mat_rank(A, t):
    return rank_f2(rows_of(A, t))


def outer(x, f, t):
    """The matrix x f^T: row r is f when x_r = 1."""
    return sum(f << (t * r) for r in range(t) if (x >> r) & 1)


def padded(basis3, t):
    """3 x 3 matrices placed in the top left corner of t x t matrices."""
    out = []
    for A in basis3:
        M = 0
        for r in range(3):
            for c in range(3):
                if (A >> (3 * r + c)) & 1:
                    M |= 1 << (t * r + c)
        out.append(M)
    return out


# ---------- covered, irreducible, the form of Lemma 28 ----------

def common_kernel_dim(basis, t):
    return t - rank_f2([r for A in basis for r in rows_of(A, t)])


def image_dim(basis, t):
    """dim of the span of the images of the elements."""
    return rank_f2([c for A in basis for c in columns_of(A, t)])


def compressions(basis, t):
    """Every (f, q) with f != 0 such that the elements map P = ker f into span(q): q is the one
    non-zero vector in the union of the A P, or 0 if every element kills P."""
    out = []
    for f in range(1, 1 << t):
        P = nullspace([f], t)
        vals = {mat_apply(A, p, t) for A in basis for p in P} - {0}
        if len(vals) <= 1:
            out.append((f, vals.pop() if vals else 0))
    return out


def proper_subspaces(t):
    """Every subspace Y with 0 < dim Y < t, as (basis, set of elements)."""
    return [(B, set(elements(B))) for c in range(1, t) for B in subspaces(t, c)]


def is_irreducible(basis, t, subs):
    return not any(all(mat_apply(A, y, t) in S for A in basis for y in B) for B, S in subs)


def classify(basis, t, subs):
    ck, im, comp = common_kernel_dim(basis, t), image_dim(basis, t), compressions(basis, t)
    return {"kernel": ck, "image": im, "compressions": len(comp),
            "covered": ck > 0 or im <= 2 or bool(comp),
            "irreducible": is_irreducible(basis, t, subs),
            "lemma28": any(q == 0 or parity(f & q) for f, q in comp)}


# ---------- the primitive spaces of M_3(F_2) (de Seguins Pazzis, Theorem 1.5) ----------
# Generic matrices, rows top to bottom: A_3 = [0 a b; a 0 c; b c 0];
# U_3 = [0 a a+c; a 0 b; a+b c 0]; V_3 = [0 a c+d; c 0 b; a+b d 0]; J_3 = [a c d; 0 a+b e; 0 0 b].
PRIMITIVE3 = {
    "A3": [[(0, 1), (1, 0)], [(0, 2), (2, 0)], [(1, 2), (2, 1)]],
    "U3": [[(0, 1), (0, 2), (1, 0), (2, 0)], [(1, 2), (2, 0)], [(0, 2), (2, 1)]],
    "V3": [[(0, 1), (2, 0)], [(1, 2), (2, 0)], [(0, 2), (1, 0)], [(0, 2), (2, 1)]],
    "J3": [[(0, 0), (1, 1)], [(1, 1), (2, 2)], [(0, 1)], [(0, 2)], [(1, 2)]],
}


def primitive3(name):
    return [entries(3, cells) for cells in PRIMITIVE3[name]]


def random_rank2(rng, t):
    return outer(rng.randrange(1, 1 << t), rng.randrange(1, 1 << t), t) ^ \
        outer(rng.randrange(1, 1 << t), rng.randrange(1, 1 << t), t)


def grow(rng, t, basis, tries):
    """Extend basis by random matrices of rank <= 2 as long as every element keeps rank <= 2."""
    basis = list(basis)
    elems = elements(basis)
    seen = set(elems)
    for _ in range(tries):
        m = random_rank2(rng, t)
        if m in seen:
            continue
        if all(mat_rank(m ^ e, t) <= 2 for e in elems):
            basis.append(m)
            new = [m ^ e for e in elems]
            elems += new
            seen.update(new)
    return basis


# ---------- parts ----------

def rank2_survey(budget_seconds, rng, counts=((3, 300), (4, 300), (5, 200)), tries=200):
    start = time.time()
    st = {"finished": False, "by_t": {}}
    for t, count in counts:
        subs = proper_subspaces(t)
        s = {"spaces": 0, "seeded": 0, "parts": 0, "uncovered": 0, "irreducible": 0,
             "irreducible_not_l28": 0, "seeded_kernel_ge": 0, "max_dim": {},
             "examples_uncovered": [], "examples_not_l28": []}
        st["by_t"][str(t)] = s
        for i in range(count):
            if time.time() - start > budget_seconds:
                return st
            seed = []
            if t >= 4 and i % 2:
                seed = padded(primitive3(sorted(PRIMITIVE3)[(i // 2) % 4]), t)
                s["seeded"] += 1
            B = grow(rng, t, seed, tries)
            s["spaces"] += 1
            key = str(len(B))
            s["max_dim"][key] = s["max_dim"].get(key, 0) + 1
            if seed and common_kernel_dim(B, t) >= t - 3:
                s["seeded_kernel_ge"] += 1
            for k in range(1, len(B) + 1):
                c = classify(B[:k], t, subs)
                s["parts"] += 1
                if not c["covered"]:
                    s["uncovered"] += 1
                    if len(s["examples_uncovered"]) < 5:
                        s["examples_uncovered"].append(B[:k])
                if c["irreducible"]:
                    s["irreducible"] += 1
                    if not c["lemma28"]:
                        s["irreducible_not_l28"] += 1
                        if len(s["examples_not_l28"]) < 5:
                            s["examples_not_l28"].append(B[:k])
    st["finished"] = True
    return st


def pairs_check(t=4):
    """Every 2-dimensional space of matrices of rank <= 2: up to equivalence it contains E_00 + E_11
    (if it has an element of rank 2) or E_00 (otherwise), so pair one of these with every m."""
    st = {"spaces": 0, "uncovered": 0, "examples": []}
    for N in (entries(t, [(0, 0)]), entries(t, [(0, 0), (1, 1)])):
        for m in range(1, 1 << (t * t)):
            if m == N or mat_rank(m, t) > 2 or mat_rank(m ^ N, t) > 2:
                continue
            st["spaces"] += 1
            B = [N, m]
            if not (common_kernel_dim(B, t) > 0 or image_dim(B, t) <= 2 or compressions(B, t)):
                st["uncovered"] += 1
                if len(st["examples"]) < 5:
                    st["examples"].append(B)
    return st


def control():
    subs3, out = proper_subspaces(3), {}
    for name in sorted(PRIMITIVE3):
        B = primitive3(name)
        ranks = sorted({mat_rank(A, 3) for A in elements(B) if A})
        out[name] = dict(classify(B, 3, subs3), dim=rank_f2(B), ranks=ranks)
    pad = {}
    for t in (4, 5):
        subs = proper_subspaces(t)
        for name in sorted(PRIMITIVE3):
            c = classify(padded(primitive3(name), t), t, subs)
            pad[f"{name} {t}"] = c
    graded = {f"{n}_rank2_not_covered": out[n]["ranks"][-1] == 2 and not out[n]["covered"]
              for n in out}
    graded["dims"] = [out[n]["dim"] for n in ("A3", "U3", "V3", "J3")] == [3, 3, 4, 5]
    graded["A3_irreducible"] = out["A3"]["irreducible"]
    graded["U3_V3_all_rank_2"] = out["U3"]["ranks"] == [2] and out["V3"]["ranks"] == [2]
    graded["padded_covered_reducible"] = all(c["covered"] and not c["irreducible"]
                                             for c in pad.values())
    explore = {n: {"irreducible": out[n]["irreducible"], "ranks": out[n]["ranks"]} for n in out}
    return {"spaces": out, "padded": pad, "graded": graded, "exploratory": explore}


def bounds(tmax):
    """Upper bounds A[t] >= A(t) and E[t] >= M(t) - t for t = 0..tmax (Proposition 23):
    A(1), A(2), A(3) = 1, 2, 3, and for t >= 4
    A(t) <= min(2t, max(t, t + A(t - 3), max over 0 < d < t of M(t - d) + A(d))),
    with M(s) <= s + E(s) and E(s) = max over r <= s of (A(r) - r) (Theorem 24)."""
    A, E = [0, 1, 2, 3], [0, 0, 0, 0]
    for t in range(4, tmax + 1):
        red = max(t - d + E[t - d] + A[d] for d in range(1, t))
        A.append(min(2 * t, max(t, t + A[t - 3], red)))
        E.append(max(E[t - 1], A[t] - t))
    return A[:tmax + 1], E[:tmax + 1]


def settled(a, b):
    """Corollary 16 (the count of Corollary 14 with the bounds of Proposition 23): tau = the largest
    t <= a with E[s] <= b for every s <= t."""
    if b <= 1:
        return True
    E = bounds(a)[1]
    tau = 0
    while tau < a and E[tau + 1] <= b:
        tau += 1
    return (a - tau - 2) * (b - 1) <= 1


EXTRA = {(9, 5), (9, 6), (10, 7)}


def cases():
    A, E = bounds(12)
    grid = {(a, b): settled(a, b) for a in range(1, 15) for b in range(0, 13)}
    first_open = {str(b): min([a for a in range(1, 15) if not grid[(a, b)]] or [None])
                  for b in range(2, 13)}
    return {"a_bounds": A, "e_bounds": E, "first_open": first_open,
            "graded": {"a_bounds": A[:10] == [0, 1, 2, 3, 5, 7, 9, 12, 15, 18],
                       "e_bounds": E[:10] == [0, 0, 0, 0, 1, 2, 3, 5, 7, 9],
                       "corollary16": all(v == (b <= 1 or a <= max(8, b + 2) or (a, b) in EXTRA)
                                          for (a, b), v in grid.items()),
                       "contains_corollary14": all(v for (a, b), v in grid.items()
                                                   if b <= 1 or a <= max(7, b + 2))}}


def write_out(out, out_dir, name):
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(out, f, indent=1)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--part", choices=["cases", "rank2", "pairs", "control"], default="cases")
    ap.add_argument("--budget-minutes", type=float, default=20.0)
    args = ap.parse_args()
    rng = random.Random(29)
    budget = args.budget_minutes * 60
    if args.part == "cases":
        out = cases()
        graded = out["graded"]
        print(f"cases: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY cases all_match {all(graded.values())}", flush=True)
        write_out(out, args.out_dir, "cases.json")
    elif args.part == "rank2":
        st = rank2_survey(budget, rng)
        by = st["by_t"]
        graded = {f"t{t}_{k}": by.get(t, {}).get(k, 1) == 0
                  for t in ("4", "5") for k in ("uncovered", "irreducible_not_l28")}
        graded["finished"] = st["finished"]
        explore = {t: {k: s[k] for k in ("spaces", "parts", "uncovered", "irreducible",
                                         "irreducible_not_l28", "seeded", "seeded_kernel_ge",
                                         "max_dim")} for t, s in by.items()}
        print(f"rank2: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"graded: {json.dumps(graded, sort_keys=True)}", flush=True)
        print(f"exploratory: {json.dumps(explore, sort_keys=True)}", flush=True)
        print(f"SUMMARY rank2 all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded, "exploratory": explore}, args.out_dir,
                  "rank2.json")
    elif args.part == "pairs":
        st = pairs_check(4)
        graded = {"uncovered_none": st["uncovered"] == 0}
        print(f"pairs: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY pairs all_match {all(graded.values())}", flush=True)
        write_out({"stats": st, "graded": graded}, args.out_dir, "pairs.json")
    else:
        out = control()
        print(f"control: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY control all_match {all(out['graded'].values())}", flush=True)
        write_out(out, args.out_dir, "control.json")


if __name__ == "__main__":
    main()
