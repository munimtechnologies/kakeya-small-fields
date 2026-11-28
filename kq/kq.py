# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Smallest Kakeya sets in F_q^n for small q and n, by integer programming and local search.

A Kakeya set in F_q^n contains a full line {a + t d : t in F_q} for every direction d (a point
of PG(n-1, q)).  Every inclusion-minimal Kakeya set is the union of one line per direction, so

    K(n, q) = min |union of chosen lines|  over choices of one line per direction.

Integer program (one binary x_p per point, y_l per line):

    minimise sum_p x_p   s.t.   sum_{l of direction d} y_l >= 1  for every direction d,
                                y_l <= x_p                        for every line l and p in l.

Formulation "A" is exactly this.  Formulation "B" adds y_{l0} = 1 for the line
l0 = {(t, 0, ..., 0)}: the affine group AGL(n, q) is transitive on lines, so some optimal set
contains l0 after an affine change of coordinates.  Formulations "C1" and "C2" (n >= 3) also fix
a second line: some line of K is not parallel to l0, and the stabiliser of l0 maps it either to
m1 = {(0, t, 0, ..)} (if it meets l0) or to m2 = {(0, t, 1, 0, ..)} (if it is skew to l0; translate
along l0, then rescale the third coordinate).  So the optimum is min(C1, C2).  A, B and
min(C1, C2) must all give the same optimum.

The integer programs run with scipy's HiGHS (scipy.optimize.milp) when scipy is importable.  A
pure-Python local search over line choices (always run) gives upper bounds; any set it reports
is re-checked by kq/check.py, which shares no code with this module."""
import json
import os
import random
import time

# ------------------------------------------------------------------ fields (q prime or 4)


class Field:
    def __init__(self, q):
        self.q = q
        if q == 4:
            # F_4 = F_2[a]/(a^2 + a + 1); 0, 1, a, a + 1 coded 0, 1, 2, 3; addition is XOR
            mul = [[0] * 4 for _ in range(4)]
            for x in range(4):
                for y in range(4):
                    # (x1 a + x0)(y1 a + y0) with a^2 = a + 1
                    x0, x1, y0, y1 = x & 1, x >> 1, y & 1, y >> 1
                    c0 = (x0 & y0) ^ (x1 & y1)
                    c1 = (x0 & y1) ^ (x1 & y0) ^ (x1 & y1)
                    mul[x][y] = c0 | (c1 << 1)
            self.add = [[x ^ y for y in range(4)] for x in range(4)]
            self.mul = mul
        elif q in (2, 3, 5, 7):
            self.add = [[(x + y) % q for y in range(q)] for x in range(q)]
            self.mul = [[(x * y) % q for y in range(q)] for x in range(q)]
        else:
            raise ValueError("q must be 2, 3, 4, 5 or 7")


def points(n, q):
    out = [()]
    for _ in range(n):
        out = [p + (c,) for p in out for c in range(q)]
    return out


def directions(n, q):
    """Normalised direction vectors: first non-zero coordinate equal to 1."""
    return [p for p in points(n, q) if any(p) and p[next(i for i, c in enumerate(p) if c)] == 1]


def geometry(n, q):
    """Points (index <-> tuple), directions, and for each direction its lines as sorted tuples
    of point indices (the q^(n-1) parallel classes)."""
    F = Field(q)
    pts = points(n, q)
    idx = {p: i for i, p in enumerate(pts)}
    dirs = directions(n, q)
    lines = []
    for d in dirs:
        seen = set()
        cls = []
        for p in pts:
            if idx[p] in seen:
                continue
            line = []
            for t in range(q):
                td = tuple(F.mul[t][c] for c in d)
                line.append(idx[tuple(F.add[a][b] for a, b in zip(p, td))])
            line = tuple(sorted(line))
            seen.update(line)
            cls.append(line)
        lines.append(cls)
    return pts, dirs, lines


# ------------------------------------------------------------------ local search (pure Python)

def local_search(n, q, seconds, seed=0, log=None):
    """Simulated annealing over one-line-per-direction choices, minimising the union size.
    Returns (best size, best list of point indices, stats)."""
    pts, dirs, lines = geometry(n, q)
    rng = random.Random(seed)
    D = len(dirs)
    cnt = [0] * len(pts)
    choice = [rng.randrange(len(lines[d])) for d in range(D)]
    for d in range(D):
        for p in lines[d][choice[d]]:
            cnt[p] += 1
    size = sum(1 for c in cnt if c)
    best = size
    best_set = [i for i, c in enumerate(cnt) if c]
    t_end = time.time() + seconds
    temp = 1.0
    it = 0
    restarts = 0
    last_improve = 0
    while time.time() < t_end:
        it += 1
        d = rng.randrange(D)
        old = lines[d][choice[d]]
        # delta of removing the old line
        rem = sum(1 for p in old if cnt[p] == 1)
        for p in old:
            cnt[p] -= 1
        # candidate lines: evaluate a few, take the best (ties random)
        cand = rng.sample(range(len(lines[d])), min(len(lines[d]), 6))
        bestc, bestadd = None, None
        for c in cand:
            add = sum(1 for p in lines[d][c] if cnt[p] == 0)
            if bestadd is None or add < bestadd or (add == bestadd and rng.random() < 0.5):
                bestc, bestadd = c, add
        delta = bestadd - rem
        if delta <= 0 or rng.random() < pow(2.718281828, -delta / temp):
            choice[d] = bestc
            size += delta
        for p in lines[d][choice[d]]:
            cnt[p] += 1
        if size < best:
            best = size
            best_set = [i for i, c in enumerate(cnt) if c]
            last_improve = it
            if log:
                log("  local search %d^%d: %d points (iteration %d)" % (q, n, best, it))
        temp = max(0.05, 0.999995 * temp)
        if it - last_improve > 400000:
            restarts += 1
            last_improve = it
            temp = 1.0
    return best, best_set, {"iterations": it, "restarts": restarts, "seed": seed}


# ------------------------------------------------------------------ integer program (scipy)

def have_scipy():
    try:
        import numpy  # noqa: F401
        import scipy  # noqa: F401
        from scipy.optimize import milp  # noqa: F401
        return True, "scipy %s" % scipy.__version__
    except Exception as exc:
        return False, "scipy not importable: %r" % (exc,)


def solve_milp(n, q, form, seconds, log=None):
    """Solve formulation 'A' or 'B' with HiGHS.  Returns a dict with status, best size and set,
    dual bound, nodes, seconds.  Raises ImportError without scipy."""
    import numpy as np
    from scipy import sparse
    from scipy.optimize import milp, LinearConstraint, Bounds

    pts, dirs, lines = geometry(n, q)
    P = len(pts)
    flat = [(d, l) for d in range(len(dirs)) for l in lines[d]]
    L = len(flat)
    nvar = P + L
    rows, cols, vals, lo, hi = [], [], [], [], []
    r = 0
    for d in range(len(dirs)):
        for j, (dd, _l) in enumerate(flat):
            if dd == d:
                rows.append(r)
                cols.append(P + j)
                vals.append(1.0)
        lo.append(1.0)
        hi.append(np.inf)
        r += 1
    for j, (_d, l) in enumerate(flat):
        for p in l:
            rows += [r, r]
            cols += [P + j, p]
            vals += [1.0, -1.0]
            lo.append(-np.inf)
            hi.append(0.0)
            r += 1
    A = sparse.csr_matrix((vals, (rows, cols)), shape=(r, nvar))
    lb = np.zeros(nvar)
    ub = np.ones(nvar)
    if form in ("B", "C1", "C2"):
        # fixed lines as point sets: l0 = x-axis; m1 = {(0, t, 0, ..)}, m2 = {(0, t, 1, 0, ..)}
        want = [frozenset(tuple([t] + [0] * (n - 1)) for t in range(q))]
        if form == "C1":
            want.append(frozenset(tuple([0, t] + [0] * (n - 2)) for t in range(q)))
        if form == "C2":
            want.append(frozenset(tuple([0, t, 1] + [0] * (n - 3)) for t in range(q)))
        for W in want:
            hits = [j for j, (_d, l) in enumerate(flat) if frozenset(pts[p] for p in l) == W]
            if len(hits) != 1:
                raise AssertionError("fixed line not found for form %s" % form)
            lb[P + hits[0]] = 1.0
    c = np.concatenate([np.ones(P), np.zeros(L)])
    t0 = time.time()
    res = milp(c, integrality=np.ones(nvar), bounds=Bounds(lb, ub),
               constraints=[LinearConstraint(A, np.array(lo), np.array(hi))],
               options={"time_limit": float(seconds), "disp": False, "mip_rel_gap": 0.0})
    secs = time.time() - t0
    out = {"form": form, "status": int(res.status), "message": str(res.message),
           "seconds": round(secs, 1), "vars": nvar, "constraints": r,
           "dual_bound": getattr(res, "mip_dual_bound", None),
           "nodes": getattr(res, "mip_node_count", None), "gap": getattr(res, "mip_gap", None)}
    if res.x is not None:
        x = res.x
        sel = [p for p in range(P) if x[p] > 0.5]
        out["best"] = len(sel)
        out["set"] = [list(pts[p]) for p in sel]
    if out["dual_bound"] is not None:
        out["dual_bound"] = float(out["dual_bound"])
    if log:
        log("  milp %d^%d form %s: status %s, best %s, dual bound %s, %.1fs, nodes %s" % (
            q, n, form, out["status"], out.get("best"), out["dual_bound"], secs, out["nodes"]))
    return out


# ------------------------------------------------------------------ one gate case

def run_case(n, q, out_dir, budget, forms=("A", "B"), ls_share=0.25, log=print, seed=20261128,
             tag=""):
    """Local search for budget*ls_share seconds, then the integer programs (if scipy) sharing
    the rest.  Writes out_dir/kq-<q>-<n>[-<tag>].json and returns the dict."""
    os.makedirs(out_dir, exist_ok=True)
    t0 = time.time()
    rep = {"n": n, "q": q, "forms": list(forms), "tag": tag,
           "made_with": "AI agents working in MV2's name; not checked by a human mathematician",
           "complete": False}
    ok, detail = have_scipy()
    rep["engine"] = detail
    path = os.path.join(out_dir, "kq-%d-%d%s.json" % (q, n, "-" + tag if tag else ""))

    def save():
        with open(path, "w") as fh:
            json.dump(rep, fh, indent=1)

    pts, dirs, lines = geometry(n, q)
    rep["points"], rep["directions"] = len(pts), len(dirs)
    ls_secs = budget * (ls_share if ok else 0.95)
    best, best_set, st = local_search(n, q, ls_secs, seed=seed, log=log)
    rep["local_search"] = {"best": best, "set": [list(pts[p]) for p in best_set], "stats": st,
                           "seconds": round(ls_secs, 1)}
    save()
    if ok:
        rep["milp"] = {}
        for k, form in enumerate(forms):
            left = budget - (time.time() - t0) - 5
            share = left / (len(forms) - k)
            if share < 5:
                break
            try:
                rep["milp"][form] = solve_milp(n, q, form, share, log=log)
            except Exception as exc:  # report, never hide
                rep["milp"][form] = {"error": repr(exc)}
            save()
    rep["complete"] = True
    rep["seconds"] = round(time.time() - t0, 1)
    save()
    return rep
