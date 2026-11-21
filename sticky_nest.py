# sticky_nest.py -- can a height-6 cyclic triangle built from a PAIR of quadratic-root trees beat the
# a196 sticky Kakeya base 31^(1/5)?  Exact CP-SAT minimisation of the pair value lambda over three
# nested families (pre-registration notes/prereg-sticky-nest.md, job sticky-nest-v1; context a196-a199).
#
# Setting (a188, a195-a197).  A tree of height h is a sticky map P: F_3^h -> F_3^h (coordinate j depends
# only on d_1..d_j); its slices are S_t = {P(d) + t d}.  For trees A, B of height h
#   lambda(A, B) = |A_0| + |B_0| + |B_1| + |B_2 u A_1 u A_2|,
# and N = root x^2 over (A, B, B(-e)) has |N_0| + |N_1 u N_2| = lambda(A, B) (Lemma 167), so its cyclic
# triangle is a tree of height h+2 with three slices of size lambda(A, B) and beta_s <= lambda^(1/(h+2)).
# Known: lambda_3 = kappa_4 = 31 (Theorem 81; replicated by sticky-kexact-v1), lambda_4 <= 62 via (H, H),
# 60 <= kappa_5 <= lambda_4.  A pair of height-4 trees with lambda <= 61 gives beta_s <= 61^(1/6) = 1.98407.
# The unrestricted lambda_4 model (sticky-l4-v1) found no solution <= 61 in 3 hours and proved only 28.
#
# Families (each closed under a common translation of A and B, so fixing B's translation is WLOG):
#   F2  A and B both have a quadratic root map x -> x^2 + c (any c); children free.
#   F1  F2, and A's child 2 is A's child 1 reflected:  A = x^2 over (D, E, E(-e))  (as in a196's H).
#   F0  F1, and B's child 1 is a shear of child 0:  B = x^2 over (Y, X, Z), X(e) = Y(-e) - e + w
#       (a196's height-3 tree B has this form with w = (1, 0); note nested-a196-analysis).
# F0 is inside F1, which is inside F2.  At height 3 all three contain the a196 pair (A, B) (value 31) and
# cannot go below lambda_3 = 31: these are the sanity runs.  At height 4, F1 and F2 contain (H, H) (62).
# Every solution is rebuilt in pure Python: value, family membership, stickiness, and the cyclic
# triangle's three slices counted by brute force.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Needs ortools for the solver runs; uses sticky_s7 and sticky_kexact from
# github.com/munimtechnologies/kakeya-small-fields (same directory).

import argparse
import hashlib
import json
import os

import sticky_s7 as s7
import sticky_kexact as kx

THRESH = 61
FAMILIES = ("F0", "F1", "F2")


# ---------------------------------------------------------------- family structure (pure Python)

def neg(a):
    return tuple((-y) % 3 for y in a)


def reflect_pairs(h):
    """Keys ((prefix, x) of child 2, (prefix, x) of child 1) whose values must agree when
    child2(e) = child1(-e):  maps[(2,)+a][x] = maps[(1,)+(-a)][-x]."""
    return [(((2,) + a, x), ((1,) + neg(a), (-x) % 3)) for a in kx.prefixes(h - 1) for x in range(3)]


def shear_pairs(h):
    """(key of child 1, key of child 0, depth j, x) with child1(e) = child0(-e) - e + w:
    maps[(1,)+a][x] = maps[(0,)+(-a)][-x] - x + w_j,  j = len(a)."""
    return [(((1,) + a, x), ((0,) + neg(a), (-x) % 3), len(a), x)
            for a in kx.prefixes(h - 1) for x in range(3)]


def is_quadratic_root(maps):
    r = maps[()]
    return any(all(r[x] == (x * x + c) % 3 for x in range(3)) for c in range(3))


def reflect_ok(maps, h):
    return all(maps[k2[0]][k2[1]] == maps[k1[0]][k1[1]] for k2, k1 in reflect_pairs(h))


def shear_w(maps, h):
    """The constant vector w (length h-1) with child1(e) = child0(-e) - e + w, or None."""
    vals = [set() for _ in range(h - 1)]
    for k1, k0, j, x in shear_pairs(h):
        vals[j].add((maps[k1[0]][k1[1]] - maps[k0[0]][k0[1]] + x) % 3)
    if any(len(v) != 1 for v in vals):
        return None
    return [next(iter(v)) for v in vals]


def in_family(mA, mB, fam, h):
    ok = is_quadratic_root(mA) and is_quadratic_root(mB)
    if fam in ("F0", "F1"):
        ok = ok and reflect_ok(mA, h)
    if fam == "F0":
        ok = ok and shear_w(mB, h) is not None
    return bool(ok)


# ---------------------------------------------------------------- CP-SAT model

def add_quadratic_root(m, G, tag):
    c = [m.NewBoolVar("%s_c%d" % (tag, v)) for v in range(3)]
    m.AddExactlyOne(c)
    for cv in range(3):
        for x in range(3):
            m.AddImplication(c[cv], G[((), x, (x * x + cv) % 3)])
    return c


def add_reflect_tie(m, G, h):
    for k2, k1 in reflect_pairs(h):
        for v in range(3):
            m.Add(G[(k2[0], k2[1], v)] == G[(k1[0], k1[1], v)])


def add_shear_tie(m, G, h, tag):
    W = []
    for j in range(h - 1):
        w = [m.NewBoolVar("%s_w%d_%d" % (tag, j, v)) for v in range(3)]
        m.AddExactlyOne(w)
        W.append(w)
    for k1, k0, j, x in shear_pairs(h):
        for v in range(3):
            for wv in range(3):
                u = (v + x - wv) % 3
                m.Add(G[(k1[0], k1[1], v)] == G[(k0[0], k0[1], u)]).OnlyEnforceIf(W[j][wv])
    return W


def build_family(fam, h):
    from ortools.sat.python import cp_model
    m = cp_model.CpModel()
    A = kx.new_tree(m, h, "a")
    B = kx.new_tree(m, h, "b")
    A0 = kx.new_points(m, h, "p")
    B0 = kx.new_points(m, h, "q")
    B1 = kx.new_points(m, h, "r")
    R = kx.new_points(m, h, "u")
    kx.cover(m, A, h, 0, A0)
    kx.cover(m, A, h, 1, R)
    kx.cover(m, A, h, 2, R)
    kx.cover(m, B, h, 0, B0)
    kx.cover(m, B, h, 1, B1)
    kx.cover(m, B, h, 2, R)
    add_quadratic_root(m, A, "ra")
    add_quadratic_root(m, B, "rb")
    kx.fix_translation(m, B, range(h))        # forces B's root to x^2 + 2; WLOG (common translation)
    if fam in ("F0", "F1"):
        add_reflect_tie(m, A, h)
    if fam == "F0":
        add_shear_tie(m, B, h, "sb")
    m.Minimize(sum(A0.values()) + sum(B0.values()) + sum(B1.values()) + sum(R.values()))
    return m, A, B


def solve(m, tlimit, workers):
    import math
    import time
    from ortools.sat.python import cp_model
    s = cp_model.CpSolver()
    s.parameters.max_time_in_seconds = float(tlimit)
    s.parameters.num_workers = int(workers)
    t0 = time.time()
    st = s.Solve(m)
    rec = {"status": s.StatusName(st), "seconds": round(time.time() - t0, 1), "time_limit": tlimit}
    bnd = s.BestObjectiveBound()
    rec["bound"] = int(math.ceil(bnd - 1e-6)) if math.isfinite(bnd) else None
    found = st in (cp_model.OPTIMAL, cp_model.FEASIBLE)
    rec["objective"] = int(round(s.ObjectiveValue())) if found else None
    return s, found, rec


def run_family(name, fam, h, tlimit, workers, hint=None):
    m, A, B = build_family(fam, h)
    hv = None
    hint_ok = None
    if hint is not None:
        hA, hB = kx.pair_hint(hint[0], hint[1], h)
        hv = kx.lam0(hA, hB, h)
        hint_ok = in_family(hA, hB, fam, h)
        if hint_ok:
            kx.add_hint(m, A, hA)
            kx.add_hint(m, B, hB)
    s, found, rec = solve(m, tlimit, workers)
    rec.update({"name": name, "family": fam, "h": h, "hint_value": hv, "hint_in_family": hint_ok,
                "verified_value": None})
    if found:
        mA = kx.extract(s, A, h)
        mB = kx.extract(s, B, h)
        val = kx.lam0(mA, mB, h)
        fam_ok = in_family(mA, mB, fam, h)
        N = kx.pair_tree(kx.fn_of(mA), kx.fn_of(mB))
        SN = s7.slices(N, h + 1)
        kN = len(SN[0]) + len(SN[1] | SN[2])
        T = kx.triangle(N)
        ts = [len(x) for x in s7.slices(T, h + 2)]
        sticky = s7.is_sticky(N, h + 1) and s7.is_sticky(T, h + 2)
        rec.update({"verified_value": val, "in_family": fam_ok, "N_kappa0": kN,
                    "triangle_height": h + 2, "triangle_slices": ts, "sticky": sticky,
                    "A_slices": [len(x) for x in kx.slices_of(mA, h)],
                    "B_slices": [len(x) for x in kx.slices_of(mB, h)],
                    "shear_w": shear_w(mB, h),
                    "verified_ok": bool(sticky and fam_ok and kN == val and ts == [val] * 3
                                        and val <= rec["objective"]),
                    "base_bound": round(val ** (1.0 / (h + 2)), 6),
                    "A_maps": kx.str_maps(mA), "B_maps": kx.str_maps(mB)})
    return rec


# ---------------------------------------------------------------- verdict (pre-registered)

SANITY = ("F0_h3", "F1_h3", "F2_h3")
H4 = ("F0_h4", "F1_h4", "F2_h4")
HINT_EXPECT = {"F0_h3": 31, "F1_h3": 31, "F2_h3": 31, "F1_h4": 62, "F2_h4": 62}


def verdict(recs):
    by = {r["name"]: r for r in recs}
    bugs = []
    for name, want in HINT_EXPECT.items():
        r = by.get(name)
        if r is not None and (r.get("hint_in_family") is not True or r.get("hint_value") != want):
            bugs.append("hint %s: in_family %s, value %s (expected True, %d)"
                        % (name, r.get("hint_in_family"), r.get("hint_value"), want))
    for name in SANITY:
        r = by.get(name)
        if r is None or r.get("verified_value") is None:
            bugs.append("sanity %s: no rebuilt solution" % name)
        elif r["verified_value"] < 31:
            bugs.append("sanity %s: %d is below lambda_3 = 31 (Theorem 81)" % (name, r["verified_value"]))
        elif r.get("status") == "OPTIMAL" and r["verified_value"] != 31:
            bugs.append("sanity %s: OPTIMAL %d although the a196 pair (31) is in the family"
                        % (name, r["verified_value"]))
    for r in recs:
        v = r.get("verified_value")
        if v is None:
            continue
        if not r.get("verified_ok"):
            bugs.append("%s: rebuilt solution failed its checks" % r["name"])
        if r.get("status") == "OPTIMAL" and r.get("objective") != v:
            bugs.append("%s: OPTIMAL objective %s but rebuilt value %d" % (r["name"], r.get("objective"), v))
        if r.get("bound") is not None and r["bound"] > v:
            bugs.append("%s: bound %d above a rebuilt value %d" % (r["name"], r["bound"], v))
    for name in H4:
        r = by.get(name)
        if r is not None and r.get("verified_value") is not None and r["verified_value"] < 60:
            bugs.append("%s: %d is below 60 (contradicts pi_6 >= 216000)" % (name, r["verified_value"]))
    out = {"bugs": bugs, "families": {}}
    best = None
    for name in H4:
        r = by.get(name)
        out["families"][name] = {k: (r or {}).get(k) for k in ("status", "objective", "bound",
                                                               "verified_value")}
        if r is not None and r.get("verified_value") is not None and r.get("verified_ok"):
            best = r["verified_value"] if best is None else min(best, r["verified_value"])
    out["height6_best_found"] = best
    closed = [n for n in H4 if by.get(n) is not None and by[n].get("bound") is not None
              and by[n]["bound"] >= THRESH + 1]
    out["closed_at_62_or_more"] = closed
    flags = []
    if best is not None and best <= THRESH:
        flags.append("H6-BEATS")
        out["base_upper_bound"] = round(best ** (1.0 / 6), 6)
    else:
        out["base_upper_bound"] = round(31 ** 0.2, 6)
    for n in closed:
        flags.append(n.split("_")[0] + "-CLOSED")
    out["flags"] = flags
    if bugs:
        out["verdict"] = "BUG"
    elif "H6-BEATS" in flags:
        out["verdict"] = "H6-BEATS"
    elif closed:
        out["verdict"] = "FAMILY-CLOSED"
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
    ap.add_argument("--out", default="nest.json")
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--t3", type=int, default=600)
    ap.add_argument("--t-f0", type=int, default=5400)
    ap.add_argument("--t-f1", type=int, default=5400)
    ap.add_argument("--t-f2", type=int, default=3600)
    args = ap.parse_args()
    here = os.path.dirname(os.path.abspath(__file__))
    res = {"job": "sticky-nest-v1", "prereg": "notes/prereg-sticky-nest.md",
           "made_with": "AI agents working in MV2's name; no human has checked this",
           "module_sha256": {f: sha(os.path.join(here, f)) for f in
                             ("sticky_nest.py", "sticky_s7.py", "sticky_kexact.py")},
           "complete": False, "runs": []}
    mA = kx.maps_of(s7.tree_A, 3)
    mB = kx.maps_of(s7.tree_B, 3)
    mH = kx.maps_of(s7.tree_H, 4)
    W = args.workers
    plan = [
        lambda: run_family("F0_h3", "F0", 3, args.t3, W, hint=(mA, mB)),
        lambda: run_family("F1_h3", "F1", 3, args.t3, W, hint=(mA, mB)),
        lambda: run_family("F2_h3", "F2", 3, args.t3, W, hint=(mA, mB)),
        lambda: run_family("F0_h4", "F0", 4, args.t_f0, W, hint=(mH, mH)),
        lambda: run_family("F1_h4", "F1", 4, args.t_f1, W, hint=(mH, mH)),
        lambda: run_family("F2_h4", "F2", 4, args.t_f2, W, hint=(mH, mH)),
    ]

    def dump():
        res["verdict"] = verdict(res["runs"])
        with open(args.out, "w") as fh:
            json.dump(res, fh, indent=1)

    dump()
    for step in plan:
        rec = step()
        res["runs"].append(rec)
        print(json.dumps({k: rec.get(k) for k in ("name", "status", "objective", "bound",
                                                   "verified_value", "hint_value", "hint_in_family",
                                                   "triangle_slices", "seconds")}), flush=True)
        dump()
    res["complete"] = True
    dump()
    print(json.dumps(res["verdict"]), flush=True)


if __name__ == "__main__":
    main()
