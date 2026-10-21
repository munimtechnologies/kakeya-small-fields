# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m30: the rank-3 configurations (A4) = ("A", 5), (B4) = ("B", 4) and (B5) = ("B", 5) at t = 6
with the matrix A_u itself fixed (notes/a17.md, Lemma 70), on top of the facts of job m29
(a6_r3h.py, Lemma 69) and the normal form of job m27 (a6_r3.py, Lemma 67).

Job m27 fixed sigma(u) = e_0, phi = beta(u, .) and the pair (X_1, R) = (ker A_u, Im A_u) up to the
group G of the normal form, and decided nothing at t = 6; in Case A at rank 4 (job m24, Lemma 61)
the normal forms fixed A_u itself and every instance fell in seconds. Here, for each pair orbit of
m27 (same index), the |GL_3(F_2)| = 168 matrices with kernel exactly X_1 and image exactly R are
split into classes under the stabiliser H of (X_1, R) in G: by Lemma 70, if a system in the normal
form has A_u = A, then for every g in H there is one with A_u = g A g^(-1), so one matrix per
H-orbit is enough. H is reached through Schreier generators t(s x)^(-1) s t(x) of a spanning tree
of the pair orbit (all of them for small orbits, a seeded random sample for large ones); the
classes are closures under the generators found, so each lies inside one H-orbit and the split
is complete whether or not the generators found generate H (if not, there are only more
instances). Every instance adds to m29's CNF the unit clauses A_u = A. Fixing A_u asks for rank
exactly rho, so UNSAT for every class of every orbit of a shape means: no anisotropic system with
t = 6 and dim V = 7 has an element of rank exactly 3 in that configuration. A SAT answer is checked
by brute force, in normal form, with the facts and with A_u = A, and would give A(6) = 7.

Parts: selfcheck (the selfchecks of a6_r3.py and a6_r3h.py; the matrices with given kernel and
image; the small groups by closure against Lemma 67's orders; at t = 2 and t = 4 the classes
against the exact H-orbits, H enumerated; the ranks and shapes of every element of every
anisotropic system with t = dim V = 2; the classes at t = 6, saved for the solve part), controls
(m29's, with A_u fixed; needs python-sat), solve (one shape at t = 6, round robin over the pair
orbits; needs python-sat), grade (the predictions of m30/predictions.md).

Usage: python a6_r3m.py --part selfcheck|controls|solve|grade [--shape A5|B4|B5]
                        [--budget-minutes 1] [--group-minutes 50] [--out-dir DIR] [--done-file F]
"""
import argparse
import itertools
import json
import os
import random
import subprocess
import sys
import time

import a6_r3 as r3
import a6_r3h as h
import sat_aniso as sa

T = r3.T
RHO = r3.RHO
SHAPES = r3.SHAPES
CONTROLS = h.CONTROLS
FULL_ORBIT = 400       # pair orbits up to this size use every Schreier generator
SAMPLES = 600          # larger ones use the generators at the root plus this many random ones


# ---------- matrices with a given kernel and image ----------

def identity(t):
    return sa.from_cols([1 << c for c in range(t)], t)


def complement(x1, t):
    """The standard basis vectors e_c at the non-pivot coordinates of the rref basis x1; with x1
    they span F_2^t."""
    pivots = {v.bit_length() - 1 for v in x1}
    return [1 << c for c in range(t) if c not in pivots]


def ordered_bases(r):
    """Every ordered basis of span(r), r an rref tuple: |GL_rho(F_2)| tuples."""
    rho = len(r)
    vecs = [sa.combine(list(r), c) for c in range(1, 1 << rho)]
    return [b for b in itertools.permutations(vecs, rho) if sa.rank_f2(list(b)) == rho]


def matrices(t, x1, r):
    """Every t x t matrix over F_2 with kernel exactly span(x1) and image exactly span(r), sorted;
    needs dim x1 + dim r = t. A is given by A x = 0 on x1 and by the images of the complement,
    an ordered basis of span(r): A = [0 | b] . [x1 | complement]^(-1)."""
    x1, r = r3.rref(list(x1)), r3.rref(list(r))
    if len(x1) + len(r) != t:
        raise ValueError("dim x1 + dim r must be t")
    basis = list(x1) + complement(x1, t)
    inv = sa.mat_inv(sa.from_cols(basis, t), t)
    out = []
    for b in ordered_bases(r):
        vals = [0] * len(x1) + list(b)
        out.append(sa.mat_mul(sa.from_cols(vals, t), inv, t))
    return sorted(out)


def ker_of(A, t):
    return r3.rref(sa.nullspace(sa.rows_of(A, t), t))


def im_of(A, t):
    return r3.rref([sa.mat_apply(A, 1 << c, t) for c in range(t)])


def conj(g, A, t, ginv=None):
    """g A g^(-1)."""
    if ginv is None:
        ginv = sa.mat_inv(g, t)
    return sa.mat_mul(sa.mat_mul(g, A, t), ginv, t)


# ---------- the stabiliser of a pair through Schreier generators ----------

def pair_orbit(t, shape, p, x1, r):
    """Breadth-first orbit of the pair (x1, r) under the elementary transvections of G, with a
    spanning tree. Returns (gens, points, index, parent, via): points[0] is the pair, and
    points[i] = gens[via[i]] applied to points[parent[i]]."""
    gens = r3.generators(t, shape, p)
    root = (r3.rref(list(x1)), r3.rref(list(r)))
    index = {root: 0}
    points, parent, via = [root], [-1], [-1]
    head = 0
    while head < len(points):
        a, b = points[head]
        for gi, g in enumerate(gens):
            q = (r3.image(g, a, t), r3.image(g, b, t))
            if q not in index:
                index[q] = len(points)
                points.append(q)
                parent.append(head)
                via.append(gi)
        head += 1
    return gens, points, index, parent, via


def transversal(gens, parent, via, i, t, inverse=False):
    """t(i) = g_k ... g_1, the tree generators from the root to point i (g_1 applied first), so
    that t(i) maps the root to point i; or its inverse g_1 ... g_k (the generators are
    involutions)."""
    acc = identity(t)
    while parent[i] >= 0:
        g = gens[via[i]]
        acc = sa.mat_mul(g, acc, t) if inverse else sa.mat_mul(acc, g, t)
        i = parent[i]
    return acc


def schreier(gens, points, index, parent, via, i, gi, t):
    """The Schreier generator t(s x_i)^(-1) s t(x_i) for point i and generator gi, an element of
    the stabiliser of the root; None on a tree edge (where it is the identity)."""
    s = gens[gi]
    a, b = points[i]
    j = index[(r3.image(s, a, t), r3.image(s, b, t))]
    if parent[j] == i and via[j] == gi:
        return None
    ti = transversal(gens, parent, via, i, t)
    tj_inv = transversal(gens, parent, via, j, t, inverse=True)
    return sa.mat_mul(tj_inv, sa.mat_mul(s, ti, t), t)


def classes(t, shape, p, x1, r, seed="m30", stats=None):
    """The matrices with kernel x1 and image r, partitioned by closure under conjugation by the
    Schreier generators found: [(representative = least member, sorted members)], ordered by
    representative. Each class lies inside one H-orbit."""
    gens, points, index, parent, via = pair_orbit(t, shape, p, x1, r)
    mats = matrices(t, x1, r)
    mi = {m: i for i, m in enumerate(mats)}
    uf = list(range(len(mats)))

    def find(a):
        while uf[a] != a:
            uf[a] = uf[uf[a]]
            a = uf[a]
        return a

    n = len(points)
    if n <= FULL_ORBIT:
        pairs = [(i, gi) for i in range(n) for gi in range(len(gens))]
    else:
        rng = random.Random(seed)
        pairs = [(0, gi) for gi in range(len(gens))]
        pairs += [(rng.randrange(n), rng.randrange(len(gens))) for _ in range(SAMPLES)]
    root = points[0]
    used = merges = last_merge = bad = 0
    for k, (i, gi) in enumerate(pairs):
        hg = schreier(gens, points, index, parent, via, i, gi, t)
        if hg is None:
            continue
        used += 1
        if (r3.image(hg, root[0], t), r3.image(hg, root[1], t)) != root:
            bad += 1
            continue
        hinv = sa.mat_inv(hg, t)
        for a, m in enumerate(mats):
            b = mi[conj(hg, m, t, hinv)]
            ra, rb = find(a), find(b)
            if ra != rb:
                uf[max(ra, rb)] = min(ra, rb)
                merges += 1
                last_merge = k
    groups = {}
    for a in range(len(mats)):
        groups.setdefault(find(a), []).append(mats[a])
    out = [(mats[rt], sorted(mem)) for rt, mem in sorted(groups.items())]
    if stats is not None:
        # Job m30 wrote len((rep, members)) = 2 here; the sizes in "reps" were always right.
        stats.update({"orbit_size": n, "schreier_pairs": len(pairs), "generators_used": used,
                      "not_in_stabiliser": bad, "merges": merges, "last_merge_at": last_merge,
                      "classes": len(out), "class_sizes": sorted(len(mem) for _, mem in out)})
    return out


# ---------- the exact stabiliser, for small t ----------

def group_elements(t, shape, p):
    """Every element of the group generated by the transvections of G (closure); at t <= 4 this is
    all of G (Lemma 67), and the selfcheck compares the size with Lemma 67's order."""
    gens = r3.generators(t, shape, p)
    e = identity(t)
    seen = {e}
    stack = [e]
    while stack:
        g = stack.pop()
        for s in gens:
            q = sa.mat_mul(s, g, t)
            if q not in seen:
                seen.add(q)
                stack.append(q)
    return seen


def exact_classes(t, shape, p, x1, r, G):
    """The H-orbits on the matrices, H = {g in G : g x1 = x1, g r = r} enumerated; same format as
    classes(); also |H|."""
    x1, r = r3.rref(list(x1)), r3.rref(list(r))
    H = [g for g in G if r3.image(g, x1, t) == x1 and r3.image(g, r, t) == r]
    mats = matrices(t, x1, r)
    rest = set(mats)
    out = []
    for m in mats:
        if m in rest:
            orb = {conj(g, m, t) for g in H}
            rest -= orb
            out.append((min(orb), sorted(orb)))
    return out, len(H)


# ---------- the encoding ----------

def encode_r3m(t, d, shape, p, rho, x1, r, au):
    """a6_r3h.encode_r3h (normal form, facts) plus the unit clauses A_u = au."""
    cnf, names = h.encode_r3h(t, d, shape, p, rho, x1, r)
    A = names[0][0]
    for row in range(t):
        for col in range(t):
            v = A[row][col]
            cnf.clauses.append([v] if (au >> (t * row + col)) & 1 else [-v])
    return cnf, names


def expected_control(t, rho, shape, r):
    """t = 2, dim V = 2 (Lemma 63): with A_u fixed the rank is exactly rho. Rank 0, shape A:
    SAT (u = a + b of Lemma 63 (ii), A_u = 0). Rank 1: shape B is SAT exactly for R = span(e_1)
    (u = a, A_u = E_11); shape A is UNSAT (job m27's models there had A_u = 0: a rank-1 element
    with phi(V) = span(x0) would have U+ = V of dimension 2 > k = 1, against Lemma 30; directly,
    (*) forces A_(h_1) x0 = x0 and sigma(h_1) = x0, against A_h sigma(h) = 0). At t = 4, dim V = 5
    nothing exists (A(4) = 4)."""
    if t == 2:
        if rho == 0:
            return "SAT"
        return "SAT" if shape == "B" and list(r) == [2] else "UNSAT"
    return "UNSAT"


# ---------- instances ----------

def instance_name(t, rho, shape, p, idx, c):
    return f"r3m_t{t}_r{rho}_{shape}{p}_o{idx:03d}_m{c:03d}"


def classes_path(out_dir, t, rho, shape, p):
    return os.path.join(out_dir, f"classes_t{t}_r{rho}_{shape}{p}.json")


def build_classes(t, rho, shape, p):
    """[{orbit, x1, r, size, reps: [[representative, class size], ...], stats}] for the pair
    orbits of a6_r3.orbits, in job m27's order."""
    out = []
    for idx, (x1, r, size) in enumerate(r3.orbits(t, shape, p, rho)):
        st = {}
        cl = classes(t, shape, p, x1, r, seed=f"m30-{t}-{shape}{p}-{idx}", stats=st)
        out.append({"orbit": idx, "x1": list(x1), "r": list(r), "size": size,
                    "reps": [[rep, len(mem)] for rep, mem in cl], "stats": st})
    return out


def load_classes(out_dir, t, rho, shape, p):
    path = classes_path(out_dir, t, rho, shape, p) if out_dir else None
    if path and os.path.exists(path):
        with open(path) as f:
            return json.load(f)
    data = build_classes(t, rho, shape, p)
    if path:
        with open(path, "w") as f:
            json.dump(data, f)
    return data


def specs(t, d, rho, shape, p, out_dir=None):
    """One instance per class, ordered round robin: the first class of every pair orbit, then the
    second, ... (as job m25 did), so every pair orbit gets at least one run."""
    out = []
    for o in load_classes(out_dir, t, rho, shape, p):
        for c, (rep, csize) in enumerate(o["reps"]):
            out.append({"t": t, "d": d, "rho": rho, "shape": shape, "p": p, "x1": o["x1"],
                        "r": o["r"], "size": o["size"], "au": rep, "class_size": csize,
                        "orbit": o["orbit"], "cls": c,
                        "name": instance_name(t, rho, shape, p, o["orbit"], c)})
    out.sort(key=lambda sp: (sp["cls"], sp["orbit"]))
    return out


def child(spec_path, solver, path):
    from pysat.solvers import Solver
    with open(spec_path) as f:
        sp = json.load(f)
    t, d = sp["t"], sp["d"]
    cnf, names = encode_r3m(t, d, sp["shape"], sp["p"], sp["rho"], sp["x1"], sp["r"], sp["au"])
    start = time.time()
    used = None
    for name in (sa.SOLVERS if solver == "auto" else (solver,)):
        try:
            s = Solver(name=name, bootstrap_with=cnf.clauses)
            used = name
            break
        except Exception:
            continue
    if used is None:
        raise RuntimeError("no SAT solver available")
    ok = s.solve()
    res = {"status": "SAT" if ok else "UNSAT", "solver": used, "vars": cnf.nv,
           "clauses": len(cnf.clauses), "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, t, d)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_one(spec, solver, budget_seconds, out_dir):
    t, d, rho, shape, p = spec["t"], spec["d"], spec["rho"], spec["shape"], spec["p"]
    name = spec["name"]
    spec_path = os.path.join(out_dir, name + ".spec.json")
    with open(spec_path, "w") as f:
        json.dump(spec, f)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", spec_path,
           "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update(spec)
    res["invariants"] = r3.invariants(t, shape, p, spec["x1"], spec["r"])
    res["wall_seconds"] = round(time.time() - start, 2)
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and r3.in_normal_form(As, ss, B, t, d, shape, p, spec["x1"], spec["r"]))
        plain, alts = h.facts(t, d, shape, p, rho, spec["x1"], spec["r"])
        res["facts_hold"] = h.facts_hold(plain, alts, As, t)
        res["au_matches"] = As[0] == spec["au"]
        res["facts"] = r3.model_facts(As, ss, B, t, d)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run_group(sps, solver, budget_seconds, group_seconds, out_dir):
    """The instances in order; once the group budget is used up the rest are SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for sp in sps:
        left = group_seconds - (time.time() - start)
        if left < 1:
            res = dict(sp, status="SKIPPED")
            with open(os.path.join(out_dir, sp["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(sp, solver, min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


# ---------- selfcheck ----------

# Hand values (m30/predictions.md).
HAND_MATRICES = {0: 1, 1: 1, 2: 6, 3: 168}                       # |GL_rho(F_2)|
HAND_SMALL_GROUPS = {(2, "A", 1): 2, (2, "B", 1): 1, (4, "A", 3): 192, (4, "B", 3): 168,
                     (4, "B", 2): 48}                              # Lemma 67's formula
HAND_PAIR_ORBITS = {(2, 1, "A", 1): 2, (2, 1, "B", 1): 3, (2, 0, "A", 1): 1, (4, 2, "A", 3): 12,
                    (4, 2, "B", 3): 7, (4, 2, "B", 2): 19, (6, 3, "A", 5): 22, (6, 3, "B", 4): 39,
                    (6, 3, "B", 5): 11}                            # jobs m27 and m29
SAMPLE_CASES = ((2, (1,), (2,)), (2, (1, 2), ()), (4, (1, 2), (4, 8)),
                (6, (1, 2, 4), (8, 16, 32)))                       # (t, x1, r): rho = 1, 0, 2, 3


def t2_ranks_and_shapes():
    """For every anisotropic system with t = dim V = 2 and every u != 0: rank of A_u and the shape
    ("A"/"B", p) of u; counts by "r<rank>_<shape><p>"."""
    counts = {}
    for at, sv in h.all_t2_systems():
        for u in range(1, 4):
            x0 = sv[u]
            phi = [sv[u ^ v] ^ x0 ^ sv[v] for v in range(4)]
            P = r3.rref(phi)
            shape = "A" if r3.in_span(P, x0) else "B"
            key = f"r{sa.rank_f2(sa.rows_of(at[u], 2))}_{shape}{len(P)}"
            counts[key] = counts.get(key, 0) + 1
    return counts


def selfcheck(out_dir=None):
    st = {"r3": all(r3.selfcheck()["graded"].values()),
          "r3h": all(h.selfcheck()["graded"].values()), "matrices": {}, "small_groups": {},
          "exact": {}, "t2": t2_ranks_and_shapes(), "t6": {}}
    for t, x1, r in SAMPLE_CASES:
        xx, rr = r3.rref(list(x1)), r3.rref(list(r))
        ms = matrices(t, xx, rr)
        st["matrices"][f"t{t}_r{len(rr)}"] = {
            "count": len(ms), "distinct": len(set(ms)),
            "exact": all(ker_of(A, t) == xx and im_of(A, t) == rr for A in ms)}
    for (t, s, p), n in HAND_SMALL_GROUPS.items():
        st["small_groups"][f"t{t}_{s}{p}"] = [len(group_elements(t, s, p)), r3.group_order(t, s, p)]
    for t, d, rho, s, p in CONTROLS:
        G = group_elements(t, s, p)
        rows = []
        for idx, (x1, r, size) in enumerate(r3.orbits(t, s, p, rho)):
            cl = classes(t, s, p, x1, r, seed=f"m30-{t}-{s}{p}-{idx}")
            ex, hsize = exact_classes(t, s, p, x1, r, G)
            rows.append({"orbit": idx, "size": size, "classes": len(cl), "H": hsize,
                         "equal": [mem for _, mem in cl] == [mem for _, mem in ex],
                         "H_is_G_over_size": hsize * size == len(G)})
        st["exact"][f"t{t}_r{rho}_{s}{p}"] = rows
    pair_counts = {}
    for t, d, rho, s, p in CONTROLS:
        pair_counts[f"t{t}_r{rho}_{s}{p}"] = len(st["exact"][f"t{t}_r{rho}_{s}{p}"])
    t6 = {}
    for key, (s, p) in SHAPES.items():
        start = time.time()
        data = load_classes(out_dir, T, RHO, s, p)
        go = r3.group_order(T, s, p)
        t6[key] = {"pair_orbits": len(data), "classes": sum(len(o["reps"]) for o in data),
                   "seconds": round(time.time() - start, 1),
                   "per_orbit": [{"orbit": o["orbit"], "size": o["size"],
                                  "classes": len(o["reps"]), "stats": o["stats"]} for o in data],
                   "stabilisers_integral": all(go % o["size"] == 0 for o in data),
                   "sizes_divide_H": all((go // o["size"]) % c == 0
                                         for o in data for _, c in o["reps"]),
                   "sizes_add_up": all(sum(c for _, c in o["reps"]) == 168 for o in data),
                   "all_in_stabiliser": all(o["stats"]["not_in_stabiliser"] == 0 for o in data),
                   "late_merges": sum(1 for o in data
                                      if o["stats"]["last_merge_at"] > 0.75 * o["stats"]["schreier_pairs"])}
        pair_counts[f"t{T}_r{RHO}_{s}{p}"] = len(data)
    st["t6"] = t6
    st["pair_counts"] = pair_counts
    st["graded"] = {
        "r3_selfcheck": st["r3"],
        "r3h_selfcheck": st["r3h"],
        "matrix_counts": all(v["count"] == HAND_MATRICES[int(k.split("_r")[1])] == v["distinct"]
                             and v["exact"] for k, v in st["matrices"].items())
                         and len(st["matrices"]) >= 4,
        "small_groups": all(v[0] == v[1] == n for (t, s, p), n in HAND_SMALL_GROUPS.items()
                            for v in [st["small_groups"][f"t{t}_{s}{p}"]]),
        "exact_classes": all(row["equal"] and row["H_is_G_over_size"]
                             for rows in st["exact"].values() for row in rows),
        "pair_orbits": all(pair_counts[f"t{t}_r{rho}_{s}{p}"] == n
                           for (t, rho, s, p), n in HAND_PAIR_ORBITS.items()),
        "t2_no_rank1_shapeA": "r1_A1" not in st["t2"] and st["t2"].get("r1_B1", 0) > 0
                              and st["t2"].get("r0_A1", 0) > 0,
        "t6_stabilisers": all(v["stabilisers_integral"] and v["sizes_divide_H"]
                              and v["sizes_add_up"] and v["all_in_stabiliser"]
                              for v in t6.values())}
    return st


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if (fn.startswith("r3m_") and fn.endswith(".json") and not fn.endswith(".child.json")
                and not fn.endswith(".spec.json")):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    for name, r in results.items():
        if r.get("t") == T:
            continue
        s = r.get("status", "missing")
        if s in ("SAT", "UNSAT"):
            graded[name] = s == expected_control(r["t"], r["rho"], r["shape"], r["r"])
            if s == "SAT":
                graded[name + "_verified"] = bool(r.get("verified"))
                graded[name + "_facts_hold"] = bool(r.get("facts_hold"))
                graded[name + "_au_matches"] = bool(r.get("au_matches"))
        else:
            ungraded[name] = s
    per_shape = {}
    for key, (s, p) in SHAPES.items():
        st = [r for n, r in sorted(results.items()) if r.get("t") == T and r["shape"] == s
              and r["p"] == p]
        status = [r.get("status") for r in st]
        orbits_ = {}
        for r in st:
            o = orbits_.setdefault(r["orbit"], {"run": 0, "unsat": 0, "unknown": 0, "skipped": 0})
            o["run"] += r.get("status") in ("SAT", "UNSAT", "UNKNOWN")
            o["unsat"] += r.get("status") == "UNSAT"
            o["unknown"] += r.get("status") == "UNKNOWN"
            o["skipped"] += r.get("status") == "SKIPPED"
        per_shape[key] = {"instances": len(st),
                          "counts": {x: status.count(x) for x in sorted(set(status))},
                          "all_unsat": bool(st) and all(x == "UNSAT" for x in status),
                          "per_orbit": orbits_,
                          "undecided": [r["name"] for r in st if r.get("status") != "UNSAT"]}
        for r in st:
            if r.get("status") == "SAT":
                graded[r["name"] + "_verified"] = bool(r.get("verified"))
                graded[r["name"] + "_facts_hold"] = bool(r.get("facts_hold"))
                graded[r["name"] + "_au_matches"] = bool(r.get("au_matches"))
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    return {"graded": graded, "ungraded": ungraded, "per_shape": per_shape, "times": times,
            "any_sat_6": any(r.get("status") == "SAT" for r in results.values()
                             if r.get("t") == T)}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--shape", choices=sorted(SHAPES), default="A5")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=1.0)
    ap.add_argument("--group-minutes", type=float, default=50.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="spec.json")
    ap.add_argument("--child-out", default="child.json")
    ap.add_argument("--done-file", default="", help="instance names to skip, one per line")
    args = ap.parse_args()
    if args.part == "child":
        child(args.spec, args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        sps = [sp for t, d, rho, s, p in CONTROLS for sp in specs(t, d, rho, s, p)]
        out = run_group(sps, args.solver, 120, 3600, args.out_dir)
        print(f"SUMMARY controls instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "solve":
        s, p = SHAPES[args.shape]
        sps = specs(T, T + 1, RHO, s, p, args.out_dir)
        if args.done_file:
            with open(args.done_file) as f:
                done = {line.strip() for line in f if line.strip()}
            sps = [sp for sp in sps if sp["name"] not in done]
        out = run_group(sps, args.solver, args.budget_minutes * 60, args.group_minutes * 60,
                        args.out_dir)
        print(f"SUMMARY solve {args.shape} instances {len(sps)} {json.dumps(out, sort_keys=True)}",
              flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_6 {out['any_sat_6']} "
              + " ".join(f"{k} {v['counts']}" for k, v in out["per_shape"].items()), flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck(args.out_dir)
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())} "
              + " ".join(f"{k} orbits {v['pair_orbits']} classes {v['classes']}"
                         for k, v in st["t6"].items()), flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
