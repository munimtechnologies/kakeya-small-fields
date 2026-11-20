# sticky_kexact.py -- exact values of kappa_h and of the pair value lambda_h for sticky trees over
# F_3, by CP-SAT (pre-registration notes/prereg-sticky-kexact.md, job sticky-kexact-v1).
#
# Setting (a188, a195, a196).  A tree of height h is a map P: F_3^h -> F_3^h whose coordinate j
# depends only on d_1..d_j; its slices are S_t = {P(d) + t d}.  kappa(P) = min over i, w of
# |S_i| + |S_{i+1} u (S_{i+2} + w)| and kappa_h = min over trees.  The cyclic triangle of P
# (Proposition 89) is a tree of height h+1 with three slices of size kappa(P), so the sticky
# Kakeya base satisfies beta_s <= kappa_h^(1/(h+1)).  Theorem 79 (a196): kappa_4 <= 31.
#
# Lemma 166 (note a197).  kappa_h = min over trees P of |S_0(P)| + |S_1(P) u S_2(P)|.
#   rho_i(P) = P + i d rotates the slices, and R(d) = P(d + e) + e has S_t(R) = S_t(P) + (1 - t) e,
#   so (i, w) is moved to (0, 0) by i and e = -w.
# Lemma 167 (note a197).  For height-h trees A, B let
#   lambda(A, B) = |A_0| + |B_0| + |B_1| + |B_2 u A_1 u A_2|        (A may be translated freely)
# and lambda_h = min.  The tree N = root x^2 over (A, B, B(-e)) has
#   |N_0| + |N_1 u N_2| = lambda(A, B),
# and with Proposition 92 (a196) every height-4 tree with kappa <= 31 has value >= lambda_3.
# Since lambda_3 <= 31, kappa_4 = lambda_3.
#
# Models (all exact for the quantity they name; translations are fixed per depth):
#   kappa(h)          min |S_0| + |S_1 u S_2| over all trees of height h          (= kappa_h)
#   kappa_rooted(h)   the same with the root map fixed to x -> x^2                (>= kappa_h)
#   pair(h)           min lambda(A, B) over pairs of trees of height h            (= lambda_h)
# Every solution is rebuilt in pure Python and its cyclic triangle is counted by brute force.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Needs ortools for the solver runs; everything else is stdlib.

import argparse
import itertools
import json
import math
import time

import sticky_s7 as s7


# ---------------------------------------------------------------- trees as value tables

def prefixes(h):
    out = []
    for j in range(h):
        out.extend(itertools.product(range(3), repeat=j))
    return out


def pts(h):
    return list(itertools.product(range(3), repeat=h))


def maps_of(P, h):
    """maps[a][x] = coordinate len(a) of P at any direction starting with a + (x,)."""
    out = {}
    for a in prefixes(h):
        j = len(a)
        out[a] = tuple(P(a + (x,) + (0,) * (h - j - 1))[j] % 3 for x in range(3))
    return out


def fn_of(maps):
    def P(d):
        d = tuple(d)
        return tuple(maps[d[:j]][d[j]] for j in range(len(d)))
    return P


def shift_maps(maps, c):
    """Translate the tree by the vector c (adds c_j to every value at depth j)."""
    return {a: tuple((v + c[len(a)]) % 3 for v in g) for a, g in maps.items()}


def norm_vec(maps, h, depths):
    c = [0] * h
    for j in depths:
        c[j] = (-maps[(1,) * j][1]) % 3
    return c


def normalised(maps, h, depths):
    return shift_maps(maps, norm_vec(maps, h, depths))


def slices_of(maps, h):
    return s7.slices(fn_of(maps), h)


def kappa0(maps, h):
    S = slices_of(maps, h)
    return len(S[0]) + len(S[1] | S[2])


def lam0(mA, mB, h):
    SA = slices_of(mA, h)
    SB = slices_of(mB, h)
    return len(SA[0]) + len(SB[0]) + len(SB[1]) + len(SB[2] | SA[1] | SA[2])


def lam_best(mA, mB, h):
    """(lambda with the best translation v of A, v)."""
    SA = slices_of(mA, h)
    SB = slices_of(mB, h)
    U = SA[1] | SA[2]
    best = None
    for v in pts(h):
        n = len(SB[2] | s7.translate(U, v))
        if best is None or n < best[0]:
            best = (n, v)
    return len(SA[0]) + len(SB[0]) + len(SB[1]) + best[0], best[1]


def pair_hint(mA, mB, h):
    """Place A at its best translation, then normalise the pair by one global translation."""
    _, v = lam_best(mA, mB, h)
    A1 = shift_maps(mA, list(v))
    c = norm_vec(mB, h, range(h))
    return shift_maps(A1, c), shift_maps(mB, c)


def triangle(P):
    """Cyclic triangle (Proposition 89, i = 0, w = 0): root x^2 over (P, P + 2d, P + d)."""
    kids = (P, s7.rho(P, 2), s7.rho(P, 1))

    def T(d):
        return (d[0] * d[0] % 3,) + tuple(kids[d[0]](tuple(d[1:])))
    return T


def pair_tree(PA, PB):
    """N = root x^2 over (A, B, B(-e))."""
    def PC(e):
        return PB(tuple((-x) % 3 for x in e))
    kids = (PA, PB, PC)

    def N(d):
        return (d[0] * d[0] % 3,) + tuple(kids[d[0]](tuple(d[1:])))
    return N


def str_maps(maps):
    return {("".join(map(str, a)) or "root"): list(g) for a, g in sorted(maps.items())}


# ---------------------------------------------------------------- CP-SAT models

def new_tree(m, h, tag):
    G = {}
    for a in prefixes(h):
        nm = tag + ("".join(map(str, a)) or "r")
        for x in range(3):
            lits = [m.NewBoolVar("%s_%d_%d" % (nm, x, v)) for v in range(3)]
            m.AddExactlyOne(lits)
            for v in range(3):
                G[(a, x, v)] = lits[v]
    return G


def new_points(m, h, tag):
    return {z: m.NewBoolVar(tag + "".join(map(str, z))) for z in pts(h)}


def cover(m, G, h, t, target):
    """For every direction d: P(d) + t d lies in target."""
    P = pts(h)
    for d in P:
        for z in P:
            lits = [G[(d[:j], d[j], (z[j] - t * d[j]) % 3)].Not() for j in range(h)]
            m.AddBoolOr(lits + [target[z]])


def fix_translation(m, G, depths):
    for j in depths:
        m.Add(G[((1,) * j, 1, 0)] == 1)


def add_hint(m, G, maps):
    for (a, x, v), lit in G.items():
        m.AddHint(lit, 1 if maps[a][x] == v else 0)


def extract(s, G, h):
    return {a: tuple(next(v for v in range(3) if s.Value(G[(a, x, v)])) for x in range(3))
            for a in prefixes(h)}


def build_kappa(h, rooted):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    G = new_tree(m, h, "g")
    S0 = new_points(m, h, "s")
    U = new_points(m, h, "u")
    cover(m, G, h, 0, S0)
    cover(m, G, h, 1, U)
    cover(m, G, h, 2, U)
    if rooted:
        for x in range(3):
            m.Add(G[((), x, x * x % 3)] == 1)
        fix_translation(m, G, range(1, h))
    else:
        fix_translation(m, G, range(h))
    m.Minimize(sum(S0.values()) + sum(U.values()))
    return m, G


def build_pair(h):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    A = new_tree(m, h, "a")
    B = new_tree(m, h, "b")
    A0 = new_points(m, h, "p")
    B0 = new_points(m, h, "q")
    B1 = new_points(m, h, "r")
    R = new_points(m, h, "u")
    cover(m, A, h, 0, A0)
    cover(m, A, h, 1, R)
    cover(m, A, h, 2, R)
    cover(m, B, h, 0, B0)
    cover(m, B, h, 1, B1)
    cover(m, B, h, 2, R)
    fix_translation(m, B, range(h))
    m.Minimize(sum(A0.values()) + sum(B0.values()) + sum(B1.values()) + sum(R.values()))
    return m, A, B


def _solve(m, tlimit, workers):
    from ortools.sat.python import cp_model
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = float(tlimit)
    s.parameters.num_workers = int(workers)
    t0 = time.time()
    st = s.Solve(m)
    rec = {"status": s.StatusName(st), "seconds": round(time.time() - t0, 1),
           "time_limit": tlimit}
    bnd = s.BestObjectiveBound()
    rec["bound"] = int(math.ceil(bnd - 1e-6)) if math.isfinite(bnd) else None
    found = st in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    rec["objective"] = int(round(s.ObjectiveValue())) if found else None
    return s, found, rec


def run_kappa(name, h, rooted, tlimit, workers, hint=None):
    m, G = build_kappa(h, rooted)
    hv = None
    if hint is not None:
        hm = normalised(hint, h, range(1, h) if rooted else range(h))
        hv = kappa0(hm, h)
        add_hint(m, G, hm)
    s, found, rec = _solve(m, tlimit, workers)
    rec.update({"name": name, "model": "kappa_rooted" if rooted else "kappa", "h": h,
                "hint_value": hv, "verified_value": None})
    if found:
        mp = extract(s, G, h)
        P = fn_of(mp)
        val = kappa0(mp, h)
        T = triangle(P)
        ts = [len(x) for x in s7.slices(T, h + 1)]
        sticky = s7.is_sticky(P, h) and s7.is_sticky(T, h + 1)
        rec.update({"verified_value": val, "triangle_height": h + 1, "triangle_slices": ts,
                    "sticky": sticky, "root": list(mp[()]),
                    "slice_sizes": [len(x) for x in slices_of(mp, h)],
                    "verified_ok": bool(sticky and ts == [val] * 3 and val <= rec["objective"]),
                    "base_bound": round(val ** (1.0 / (h + 1)), 6),
                    "maps": str_maps(mp)})
    return rec


def run_pair(name, h, tlimit, workers, hint=None):
    m, A, B = build_pair(h)
    hv = None
    if hint is not None:
        hA, hB = pair_hint(hint[0], hint[1], h)
        hv = lam0(hA, hB, h)
        add_hint(m, A, hA)
        add_hint(m, B, hB)
    s, found, rec = _solve(m, tlimit, workers)
    rec.update({"name": name, "model": "pair", "h": h, "hint_value": hv,
                "verified_value": None})
    if found:
        mA = extract(s, A, h)
        mB = extract(s, B, h)
        val = lam0(mA, mB, h)
        N = pair_tree(fn_of(mA), fn_of(mB))
        SN = s7.slices(N, h + 1)
        kN = len(SN[0]) + len(SN[1] | SN[2])
        T = triangle(N)
        ts = [len(x) for x in s7.slices(T, h + 2)]
        sticky = s7.is_sticky(N, h + 1) and s7.is_sticky(T, h + 2)
        rec.update({"verified_value": val, "N_kappa0": kN, "triangle_height": h + 2,
                    "triangle_slices": ts, "sticky": sticky,
                    "A_slices": [len(x) for x in slices_of(mA, h)],
                    "B_slices": [len(x) for x in slices_of(mB, h)],
                    "verified_ok": bool(sticky and kN == val and ts == [val] * 3
                                        and val <= rec["objective"]),
                    "base_bound": round(val ** (1.0 / (h + 2)), 6),
                    "A_maps": str_maps(mA), "B_maps": str_maps(mB)})
    return rec


# ---------------------------------------------------------------- verdict (pre-registered)

EXPECT = {"kappa1": 4, "kappa2": 8, "kappa3": 16, "lambda2": 16}
HINTS = {"lambda3": 31, "kappa4_rooted": 31, "kappa4_direct": 31, "lambda4": 62,
         "kappa5_rooted": 62}
H4 = ("lambda3", "kappa4_rooted", "kappa4_direct")
H6 = ("lambda4", "kappa5_rooted")


def verdict(recs):
    by = {r["name"]: r for r in recs}
    bugs = []
    for name, want in EXPECT.items():
        r = by.get(name)
        if r is None or r.get("status") != "OPTIMAL" or r.get("verified_value") != want:
            bugs.append("sanity %s: expected OPTIMAL %d" % (name, want))
    for name, want in HINTS.items():
        r = by.get(name)
        if r is not None and r.get("hint_value") != want:
            bugs.append("hint %s: %s instead of %d" % (name, r.get("hint_value"), want))
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
    for name in H4:
        r = by.get(name)
        if r is not None and r.get("verified_value") is not None and r["verified_value"] < 30:
            bugs.append("%s: %d is below the proved lower bound 30 (pi_5 >= 27000)"
                        % (name, r["verified_value"]))

    def best(names):
        vals = [by[n]["verified_value"] for n in names
                if n in by and by[n].get("verified_value") is not None]
        return min(vals) if vals else None

    def exact(name):
        r = by.get(name)
        return r["verified_value"] if r is not None and r.get("status") == "OPTIMAL" else None

    out = {"bugs": bugs}
    k4 = best(H4)
    k6 = best(H6)
    out["kappa4_best_found"] = k4
    out["lambda3_exact"] = exact("lambda3")
    out["kappa4_rooted_exact"] = exact("kappa4_rooted")
    out["kappa4_direct_exact"] = exact("kappa4_direct")
    kd = by.get("kappa4_direct")
    out["kappa4_direct_bound"] = kd.get("bound") if kd is not None else None
    out["height6_best_found"] = k6
    for name in H6:
        r = by.get(name)
        out[name + "_bound"] = r.get("bound") if r is not None else None
    flags = []
    if k4 is not None and k4 <= 30:
        flags.append("KAPPA4-30")
    if out["lambda3_exact"] == 31:
        flags.append("LAMBDA3-EXACT-31")
    if out["kappa4_direct_exact"] == 31:
        flags.append("KAPPA4-EXACT-31")
    if (out["lambda3_exact"] == 31 and kd is not None and kd.get("verified_value") is not None
            and kd["verified_value"] <= 30):
        flags.append("PROP92-CONFLICT")
    if k6 is not None and k6 <= 61:
        flags.append("BASE-IMPROVED-H6")
    bases = [31 ** 0.2]
    if k4 is not None:
        bases.append(k4 ** 0.2)
    if k6 is not None:
        bases.append(k6 ** (1.0 / 6))
    out["base_upper_bound"] = round(min(bases), 6)
    out["flags"] = flags
    if bugs:
        out["verdict"] = "BUG"
    elif "KAPPA4-30" in flags or "BASE-IMPROVED-H6" in flags:
        out["verdict"] = "BASE-IMPROVED"
    elif "LAMBDA3-EXACT-31" in flags or "KAPPA4-EXACT-31" in flags:
        out["verdict"] = "KAPPA4-31"
    else:
        out["verdict"] = "UNDECIDED"
    return out


# ---------------------------------------------------------------- driver

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default="kexact.json")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--t-small", type=int, default=600)
    ap.add_argument("--t-l3", type=int, default=1800)
    ap.add_argument("--t-k4r", type=int, default=3000)
    ap.add_argument("--t-k4d", type=int, default=3000)
    ap.add_argument("--t-l4", type=int, default=3000)
    ap.add_argument("--t-k5r", type=int, default=2400)
    args = ap.parse_args()
    mA = maps_of(s7.tree_A, 3)
    mB = maps_of(s7.tree_B, 3)
    mH = maps_of(s7.tree_H, 4)
    mG = maps_of(s7.tree_G, 5)
    W = args.workers
    plan = [
        lambda: run_kappa("kappa1", 1, False, args.t_small, W),
        lambda: run_kappa("kappa2", 2, False, args.t_small, W),
        lambda: run_kappa("kappa3", 3, False, args.t_small, W),
        lambda: run_pair("lambda2", 2, args.t_small, W),
        lambda: run_pair("lambda3", 3, args.t_l3, W, hint=(mA, mB)),
        lambda: run_kappa("kappa4_rooted", 4, True, args.t_k4r, W, hint=mH),
        lambda: run_kappa("kappa4_direct", 4, False, args.t_k4d, W, hint=mH),
        lambda: run_pair("lambda4", 4, args.t_l4, W, hint=(mH, mH)),
        lambda: run_kappa("kappa5_rooted", 5, True, args.t_k5r, W, hint=mG),
    ]
    res = {"job": "sticky-kexact-v1", "prereg": "notes/prereg-sticky-kexact.md",
           "made_with": "AI agents working in MV2's name; no human has checked this",
           "runs": []}

    def dump():
        res["verdict"] = verdict(res["runs"])
        with open(args.out, "w") as fh:
            json.dump(res, fh, indent=1)

    for step in plan:
        rec = step()
        res["runs"].append(rec)
        print(json.dumps({k: rec.get(k) for k in ("name", "status", "objective", "bound",
                                                   "verified_value", "hint_value",
                                                   "triangle_slices", "seconds")}),
              flush=True)
        dump()
    dump()
    print(json.dumps(res["verdict"]), flush=True)


if __name__ == "__main__":
    main()
