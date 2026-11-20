# sticky_l4.py -- can a height-6 cyclic triangle beat the a196 base 31^(1/5)?  Exact CP-SAT checks of
# lambda_4 <= 61 and kappa_5 <= 61, with the PROVED fronts of sticky-h4r-v1 as cuts.
# Pre-registration: notes/prereg-sticky-l4.md (job sticky-l4-v1).  Context: notes a195-a198.
#
# Setting (a188, a195-a197).  A tree of height h is a sticky map P: F_3^h -> F_3^h (coordinate j depends
# only on d_1..d_j); its slices are S_t = {P(d) + t d}.  kappa(P) = |S_0| + |S_1 u S_2| (Lemma 166 form)
# and kappa_h = min over trees.  The cyclic triangle of P has height h+1 and three slices of size
# kappa(P), so beta_s <= kappa_h^(1/(h+1)).  For trees A, B of height h,
#   lambda(A, B) = |A_0| + |B_0| + |B_1| + |B_2 u A_1 u A_2|     (A translated freely),
# and the tree N = root x^2 over (A, B, B(-e)) has kappa(N) = lambda(A, B), so kappa_{h+1} <= lambda_h.
#
# Known (a196-a198): kappa_4 = lambda_3 = 31 (Theorem 81: pi_5 = 29,791), 60 <= kappa_5 <= lambda_4 <= 62.
# Any value <= 61 at height 5 gives beta_s <= 61^(1/6) = 1.98407 < 31^(1/5) = 1.98734.
#
# Cuts (valid by sticky-h4r-v1 / a198): every real slice vector of a height-2 tree dominates an element
# of M2 (19 vectors, exhaustive), of a height-3 tree an element of E3 (112), of a height-4 tree an
# element of F4 (670).  In the models below each tree's slice sets are SUPERSETS of its true slices
# (the solver may pad them); the cuts are imposed on the padded sizes.  Every real configuration
# satisfies them with the true sets, and every model solution contains a real configuration of no
# larger value, so each model's optimum equals the quantity it names.
#
# Models:
#   pair_cut(h, F)    min lambda over pairs of height-h trees, both with front cut F     (= lambda_h)
#   kappa_cut(h, F)   min |S_0| + |S_1 u S_2| over ALL height-h trees, written as a root
#                     map g plus three children of height h-1 (each with front cut F):
#                     S_t = union over x of {g(x) + t x} x S_t(child x)               (= kappa_h)
# Every solution is rebuilt in pure Python; its cyclic triangle is counted by brute force.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Needs ortools for the solver runs; uses sticky_s7, sticky_kexact, sticky_h3 and
# sticky_h4r from github.com/munimtechnologies/kakeya-small-fields (same directory).

import argparse
import hashlib
import json
import math
import os
import time

import sticky_s7 as s7
import sticky_kexact as kx

THRESH = 61            # a height-5 value <= 61 beats 31^(1/5)


# ---------------------------------------------------------------- fronts (as in sticky_h4r.run)

def fronts(tlimit=3000.0, log=print):
    import sticky_h3 as h3
    import sticky_h4r as h4r
    PC = h3.PC
    t0 = time.time()
    bugs = []
    G = h3.group_elements()
    tabs = h3.mask_tables(G)
    trees = list(h3.enumerate_height2())
    n_trees = len(trees)
    vecs2 = set((PC[m0], PC[m1], PC[m2]) for m0, m1, m2, _ in trees)
    TA, TB, TC = h3.build_tables(trees)
    del trees
    M2 = h3.minimal3(vecs2)
    TA = h3.inclusion_minimal(TA)
    TB = h3.inclusion_minimal(TB)
    TC = h3.inclusion_minimal(TC)
    Creps = h3.orbit_reps(TC, tabs)
    everything = lambda L: True
    found, complete, stats = h3.exact_quadratic(TA, TB, Creps, everything, (27, 27, 27),
                                                tlimit=tlimit, log=log)
    QF = h3.minimal3(found.keys())
    AF = h3.affine_relaxed(M2, everything)
    E3 = h3.minimal3(set(QF) | AF)
    F4 = h4r.next_front(E3)
    prod = lambda v: v[0] * v[1] * v[2]
    info = {"height2_trees": n_trees, "height2_vectors": len(vecs2), "M2": len(M2),
            "E3": len(E3), "E3_complete": complete, "F4": len(F4),
            "F4_min_product": min(prod(v) for v in F4) if F4 else None,
            "seconds": round(time.time() - t0, 1)}
    if n_trees != 27 ** 4 or len(vecs2) != 96 or len(M2) != 19:
        bugs.append("height-2 counts differ from a189 (531441, 96, 19)")
    if not complete or len(E3) != 112:
        bugs.append("E3 differs from sticky-h4r-v1 (112 vectors, complete)")
    if len(F4) != 670 or info["F4_min_product"] != 4096:
        bugs.append("F4 differs from sticky-h4r-v1 (670 vectors, least product 4096)")
    return ([tuple(v) for v in M2], [tuple(v) for v in E3], [tuple(v) for v in F4]), info, bugs


def height1_front():
    """All slice vectors of height-1 trees (every map g: F_3 -> F_3), coordinatewise-minimal."""
    vecs = set()
    for g in itertools_product3():
        vecs.add(tuple(len({(g[x] + t * x) % 3 for x in range(3)}) for t in range(3)))
    return minimal(vecs)


def itertools_product3():
    return [(a, b, c) for a in range(3) for b in range(3) for c in range(3)]


def leq(u, v):
    return u[0] <= v[0] and u[1] <= v[1] and u[2] <= v[2]


def minimal(vecs):
    out = []
    for v in sorted(set(tuple(x) for x in vecs)):
        if not any(leq(f, v) for f in out):
            out.append(v)
    return out


def dominates_some(v, F):
    return any(leq(f, v) for f in F)


# ---------------------------------------------------------------- trees as root + children

def split(maps):
    """maps of a height-h tree -> (root tuple, [child maps of height h-1 for x = 0, 1, 2])."""
    kids = [{a[1:]: g for a, g in maps.items() if len(a) >= 1 and a[0] == x} for x in range(3)]
    return tuple(maps[()]), kids


def assemble(root, kids):
    maps = {(): tuple(root)}
    for x in range(3):
        for a, g in kids[x].items():
            maps[(x,) + tuple(a)] = tuple(g)
    return maps


def slices_from_children(root, kid_slices):
    """S_t of the parent from the children's slices: union over x of {g(x) + t x} x S_t(child x)."""
    out = []
    for t in range(3):
        S = set()
        for x in range(3):
            p = (root[x] + t * x) % 3
            for z in kid_slices[x][t]:
                S.add((p,) + tuple(z))
        out.append(S)
    return out


# ---------------------------------------------------------------- CP-SAT models

def add_front_cut(m, sizes, F, tag):
    ys = []
    for i, f in enumerate(F):
        y = m.NewBoolVar("%s_f%d" % (tag, i))
        for t in range(3):
            m.Add(sizes[t] >= f[t]).OnlyEnforceIf(y)
        ys.append(y)
    m.AddBoolOr(ys)


def build_pair_cut(h, F, cap=None):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    A = kx.new_tree(m, h, "a")
    B = kx.new_tree(m, h, "b")
    SA = [kx.new_points(m, h, "sa%d_" % t) for t in range(3)]
    SB = [kx.new_points(m, h, "sb%d_" % t) for t in range(3)]
    R = kx.new_points(m, h, "u")
    for t in range(3):
        kx.cover(m, A, h, t, SA[t])
        kx.cover(m, B, h, t, SB[t])
    for z in kx.pts(h):
        for X in (SA[1], SA[2], SB[2]):
            m.AddImplication(X[z], R[z])
    kx.fix_translation(m, B, range(h))
    nA = [sum(SA[t].values()) for t in range(3)]
    nB = [sum(SB[t].values()) for t in range(3)]
    nR = sum(R.values())
    for x in (nA[1], nA[2], nB[2]):
        m.Add(nR >= x)
    if F is not None:
        add_front_cut(m, nA, F, "fa")
        add_front_cut(m, nB, F, "fb")
    obj = nA[0] + nB[0] + nB[1] + nR
    if cap is not None:
        m.Add(obj <= cap)
    m.Minimize(obj)
    return m, A, B


def build_kappa_cut(h, F, cap=None):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    k = h - 1
    root = [[m.NewBoolVar("r%d_%d" % (x, v)) for v in range(3)] for x in range(3)]
    for x in range(3):
        m.AddExactlyOne(root[x])
    K = [kx.new_tree(m, k, "k%d_" % x) for x in range(3)] if k >= 1 else [{}, {}, {}]
    C = [[kx.new_points(m, k, "c%d%d_" % (x, t)) for t in range(3)] for x in range(3)]
    for x in range(3):
        for t in range(3):
            kx.cover(m, K[x], k, t, C[x][t])
    zs = kx.pts(k)
    S0 = {(p,) + z: m.NewBoolVar("s0_%d%s" % (p, "".join(map(str, z)))) for p in range(3) for z in zs}
    U = {(p,) + z: m.NewBoolVar("u_%d%s" % (p, "".join(map(str, z)))) for p in range(3) for z in zs}
    for x in range(3):
        for t in range(3):
            target = S0 if t == 0 else U
            nC = sum(C[x][t].values())
            for p in range(3):
                lit = root[x][(p - t * x) % 3]          # g(x) + t x = p
                for z in zs:
                    m.AddBoolOr([lit.Not(), C[x][t][z].Not(), target[(p,) + z]])
                m.Add(sum(target[(p,) + z] for z in zs) >= nC).OnlyEnforceIf(lit)
    m.Add(root[1][0] == 1)
    if k >= 1:
        kx.fix_translation(m, K[1], range(k))
    if F is not None:
        for x in range(3):
            add_front_cut(m, [sum(C[x][t].values()) for t in range(3)], F, "f%d" % x)
    obj = sum(S0.values()) + sum(U.values())
    if cap is not None:
        m.Add(obj <= cap)
    m.Minimize(obj)
    return m, root, K


def solve(m, tlimit, workers, cap=None):
    from ortools.sat.python import cp_model
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = float(tlimit)
    s.parameters.num_workers = int(workers)
    t0 = time.time()
    st = s.Solve(m)
    rec = {"status": s.StatusName(st), "seconds": round(time.time() - t0, 1), "time_limit": tlimit,
           "cap": cap}
    found = st in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    if st == cp_model.INFEASIBLE:
        rec["bound"] = (cap + 1) if cap is not None else None
    else:
        bnd = s.BestObjectiveBound()
        rec["bound"] = int(math.ceil(bnd - 1e-6)) if (found or st == cp_model.UNKNOWN) and \
            math.isfinite(bnd) else None
    rec["objective"] = int(round(s.ObjectiveValue())) if found else None
    return s, found, rec


def run_pair_cut(name, h, F, tlimit, workers, hint=None, cap=None):
    m, A, B = build_pair_cut(h, F, cap)
    hv = None
    if hint is not None:
        hA, hB = kx.pair_hint(hint[0], hint[1], h)
        hv = kx.lam0(hA, hB, h)
        if cap is None or hv <= cap:
            kx.add_hint(m, A, hA)
            kx.add_hint(m, B, hB)
    s, found, rec = solve(m, tlimit, workers, cap)
    rec.update({"name": name, "model": "pair_cut", "h": h, "front_size": len(F) if F else 0,
                "hint_value": hv, "verified_value": None})
    if found:
        mA = kx.extract(s, A, h)
        mB = kx.extract(s, B, h)
        val = kx.lam0(mA, mB, h)
        N = kx.pair_tree(kx.fn_of(mA), kx.fn_of(mB))
        SN = s7.slices(N, h + 1)
        kN = len(SN[0]) + len(SN[1] | SN[2])
        T = kx.triangle(N)
        ts = [len(x) for x in s7.slices(T, h + 2)]
        sticky = s7.is_sticky(N, h + 1) and s7.is_sticky(T, h + 2)
        va = [len(x) for x in kx.slices_of(mA, h)]
        vb = [len(x) for x in kx.slices_of(mB, h)]
        cut_ok = F is None or (dominates_some(va, F) and dominates_some(vb, F))
        rec.update({"verified_value": val, "N_kappa0": kN, "N_slices": [len(x) for x in SN],
                    "triangle_height": h + 2, "triangle_slices": ts, "sticky": sticky,
                    "A_slices": va, "B_slices": vb, "front_cut_ok": cut_ok,
                    "verified_ok": bool(sticky and kN == val and ts == [val] * 3 and cut_ok
                                        and val <= rec["objective"]),
                    "base_bound": round(val ** (1.0 / (h + 2)), 6),
                    "A_maps": kx.str_maps(mA), "B_maps": kx.str_maps(mB)})
    return rec


def run_kappa_cut(name, h, F, tlimit, workers, hint=None, cap=None):
    m, root, K = build_kappa_cut(h, F, cap)
    hv = None
    if hint is not None:
        hm = kx.normalised(hint, h, range(h))
        hv = kx.kappa0(hm, h)
        if cap is None or hv <= cap:
            r, kids = split(hm)
            for x in range(3):
                for v in range(3):
                    m.AddHint(root[x][v], 1 if r[x] == v else 0)
                kx.add_hint(m, K[x], kids[x])
    s, found, rec = solve(m, tlimit, workers, cap)
    rec.update({"name": name, "model": "kappa_cut", "h": h, "front_size": len(F) if F else 0,
                "hint_value": hv, "verified_value": None})
    if found:
        r = tuple(next(v for v in range(3) if s.Value(root[x][v])) for x in range(3))
        kids = [kx.extract(s, K[x], h - 1) for x in range(3)]
        mp = assemble(r, kids)
        P = kx.fn_of(mp)
        val = kx.kappa0(mp, h)
        T = kx.triangle(P)
        ts = [len(x) for x in s7.slices(T, h + 1)]
        sticky = s7.is_sticky(P, h) and s7.is_sticky(T, h + 1)
        kv = [[len(x) for x in kx.slices_of(kids[x], h - 1)] for x in range(3)]
        cut_ok = F is None or all(dominates_some(v, F) for v in kv)
        rec.update({"verified_value": val, "triangle_height": h + 1, "triangle_slices": ts,
                    "sticky": sticky, "root": list(r), "children_slices": kv,
                    "slice_sizes": [len(x) for x in kx.slices_of(mp, h)], "front_cut_ok": cut_ok,
                    "verified_ok": bool(sticky and ts == [val] * 3 and cut_ok
                                        and val <= rec["objective"]),
                    "base_bound": round(val ** (1.0 / (h + 1)), 6),
                    "maps": kx.str_maps(mp)})
    return rec


# ---------------------------------------------------------------- verdict (pre-registered)

EXPECT = {"kappa3": 16, "lambda2": 16, "lambda3": 31, "kappa4": 31}
H6 = ("lambda4", "kappa5")


def verdict(recs, front_bugs):
    by = {r["name"]: r for r in recs}
    bugs = list(front_bugs)
    for name in ("kappa3", "lambda2"):
        r = by.get(name)
        if r is None or r.get("status") != "OPTIMAL" or r.get("verified_value") != EXPECT[name]:
            bugs.append("sanity %s: expected OPTIMAL %d" % (name, EXPECT[name]))
    for r in recs:
        v = r.get("verified_value")
        if v is None:
            continue
        if not r.get("verified_ok"):
            bugs.append("%s: rebuilt solution failed its checks" % r["name"])
        if r.get("status") == "OPTIMAL" and r.get("objective") != v:
            bugs.append("%s: OPTIMAL objective %s but rebuilt value %d"
                        % (r["name"], r.get("objective"), v))
        if r.get("bound") is not None and r["bound"] > v:
            bugs.append("%s: bound %d above a rebuilt value %d" % (r["name"], r["bound"], v))
    for name in ("lambda3", "kappa4"):
        r = by.get(name)
        if r is not None and r.get("verified_value") is not None and r["verified_value"] < 31:
            bugs.append("%s: %d is below 31 (contradicts pi_5 = 29791, Theorem 81)"
                        % (name, r["verified_value"]))
        if r is not None and r.get("bound") is not None and r["bound"] > 31:
            bugs.append("%s: bound %d above the known value 31" % (name, r["bound"]))
    for name in H6:
        r = by.get(name)
        if r is not None and r.get("verified_value") is not None and r["verified_value"] < 60:
            bugs.append("%s: %d is below 60 (contradicts pi_6 >= 216000)" % (name, r["verified_value"]))
    l4, k5 = by.get("lambda4"), by.get("kappa5")
    if (l4 is not None and l4.get("verified_value") is not None and l4["verified_value"] <= THRESH
            and k5 is not None and k5.get("status") == "INFEASIBLE"):
        bugs.append("kappa5 INFEASIBLE at <= 61 but lambda4 has a rebuilt value <= 61 (kappa_5 <= lambda_4)")
    out = {"bugs": bugs}
    flags = []
    for name in ("lambda3", "kappa4"):
        r = by.get(name)
        out[name] = {k: (r or {}).get(k) for k in ("status", "objective", "bound", "verified_value")}
        if r is not None and r.get("status") == "OPTIMAL" and r.get("verified_value") == 31:
            flags.append(name.upper() + "-EXACT-31")
    best = None
    for name in H6:
        r = by.get(name)
        out[name] = {k: (r or {}).get(k) for k in ("status", "objective", "bound", "verified_value")}
        if r is not None and r.get("verified_value") is not None and r.get("verified_ok"):
            best = r["verified_value"] if best is None else min(best, r["verified_value"])
    out["height5_best_found"] = best
    if best is not None and best <= THRESH:
        flags.append("H6-BEATS")
        out["base_upper_bound"] = round(best ** (1.0 / 6), 6)
    else:
        out["base_upper_bound"] = round(31 ** 0.2, 6)
    if l4 is not None and l4.get("status") == "INFEASIBLE":
        flags.append("LAMBDA4-62")
    if k5 is not None and k5.get("status") == "INFEASIBLE":
        flags.append("KAPPA5-62")
    out["flags"] = flags
    if bugs:
        out["verdict"] = "BUG"
    elif "H6-BEATS" in flags:
        out["verdict"] = "H6-BEATS"
    elif "KAPPA5-62" in flags:
        out["verdict"] = "KAPPA5-62"
    elif "LAMBDA4-62" in flags:
        out["verdict"] = "LAMBDA4-62"
    else:
        out["verdict"] = "UNDECIDED"
    return out


# ---------------------------------------------------------------- driver

def sha(path):
    try:
        with open(path, "rb") as fh:
            return hashlib.sha256(fh.read()).hexdigest()
    except OSError:
        return None


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="l4.json")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--t-small", type=int, default=600)
    ap.add_argument("--t-l3", type=int, default=1200)
    ap.add_argument("--t-k4", type=int, default=1800)
    ap.add_argument("--t-l4", type=int, default=7200)
    ap.add_argument("--t-k5", type=int, default=8400)
    args = ap.parse_args()
    here = os.path.dirname(os.path.abspath(__file__))
    res = {"job": "sticky-l4-v1", "prereg": "notes/prereg-sticky-l4.md",
           "made_with": "AI agents working in MV2's name; no human has checked this",
           "module_sha256": {f: sha(os.path.join(here, f)) for f in
                             ("sticky_l4.py", "sticky_s7.py", "sticky_kexact.py", "sticky_h3.py",
                              "sticky_h4r.py")},
           "runs": []}
    (M2, E3, F4), info, front_bugs = fronts()
    res["fronts"] = info
    res["front_bugs"] = front_bugs

    def dump():
        res["verdict"] = verdict(res["runs"], front_bugs)
        with open(args.out, "w") as fh:
            json.dump(res, fh, indent=1)

    dump()
    print(json.dumps(info), flush=True)
    if front_bugs:
        print(json.dumps(res["verdict"]), flush=True)
        return
    mA = kx.maps_of(s7.tree_A, 3)
    mB = kx.maps_of(s7.tree_B, 3)
    mH = kx.maps_of(s7.tree_H, 4)
    W = args.workers
    plan = [
        lambda: run_kappa_cut("kappa3", 3, M2, args.t_small, W),
        lambda: run_pair_cut("lambda2", 2, M2, args.t_small, W),
        lambda: run_pair_cut("lambda3", 3, E3, args.t_l3, W, hint=(mA, mB)),
        lambda: run_kappa_cut("kappa4", 4, E3, args.t_k4, W, hint=mH),
        lambda: run_pair_cut("lambda4", 4, F4, args.t_l4, W, cap=THRESH),
        lambda: run_kappa_cut("kappa5", 5, F4, args.t_k5, W, cap=THRESH),
    ]
    for step in plan:
        rec = step()
        res["runs"].append(rec)
        print(json.dumps({k: rec.get(k) for k in ("name", "status", "objective", "bound",
                                                   "verified_value", "hint_value",
                                                   "triangle_slices", "seconds")}), flush=True)
        dump()
    dump()
    print(json.dumps(res["verdict"]), flush=True)


if __name__ == "__main__":
    main()
