# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Case B of Question R split by the shapes of Proposition 27 (notes/case-b-shapes.md).

Setting and encoding as in case_b.py. Lemma 37 of notes/case-b-shapes.md: if some anisotropic system
with dim X = t and dim V = t + k - 1 has an element u = v_0 in Case B, then it has one in the normal
form of Lemma 35 in which also v_1, ..., v_(k-1) (a basis of U+ = ker phi modulo u) and their values
are fixed, according to the shape of Proposition 27. With e_0 = x0 and the bit masks e_0 = 1,
e_1 = 2, e_2 = 4:

    c     (any k >= 2) sigma(v_i) = e_i, beta(v_i, v_j) = 0, A_(v_i) kills e_0, ..., e_(k-1)
    d1    (k = 3)      sigma(v_1) = e_1, sigma(v_2) = e_2, beta(v_1, v_2) = e_0,
                       A_(v_1): e_0, e_1 -> 0, e_2 -> e_0;  A_(v_2): e_0, e_2 -> 0, e_1 -> e_0
    d2c0  (k = 3)      sigma(v_1) = e_1, sigma(v_2) = beta(v_1, v_2) = delta = e_2,
                       A_(v_1): e_0, e_1 -> 0, e_2 -> delta;  A_(v_2) kills e_0, e_1, e_2
    d2c1  (k = 3)      the same with delta = e_2 + e_0 (A_(v_1) e_2 = A_(v_1) delta = delta)

So Case B at (t, k) = (6, 3) exists iff one of the four CNFs is satisfiable, and UNSAT for all four
gives A(6) <= 7 (Corollary 18(b) of notes/tight-cases.md). The split uses Proposition 27 (by hand);
the plain search of case_b.py does not, and decides the same question.

Parts: selfcheck (pure Python: the anisotropic systems that U+ carries, classified exhaustively;
the shape values form such systems of the right shape), solve (one instance in a child process with
a time budget; needs python-sat), grade (the pre-registered predictions of m12/predictions.md).

Usage: python case_b_shapes.py --part selfcheck|solve|grade [--t T --k K --shape S]
                               [--budget-minutes 5] [--out-dir DIR]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import case_b as cb
import sat_aniso as sa

SHAPES = ("c", "d1", "d2c0", "d2c1")


# ---------- the shapes ----------

def shape_values(t, k, shape):
    """(sigma values, beta values, fixed columns) of v_1, ..., v_(k-1): {i: s}, {(i, j): b},
    {(i, c): A_(v_i) e_c}."""
    if shape == "c":
        if k < 2:
            raise ValueError("shape c needs k >= 2")
        S = {i: 1 << i for i in range(1, k)}
        B = {(i, j): 0 for i, j in itertools.combinations(range(1, k), 2)}
        C = {(i, c): 0 for i in range(1, k) for c in range(k)}
        return S, B, C
    if k != 3 or t < 3:
        raise ValueError("shapes d1 and d2 need k = 3")
    if shape == "d1":
        return ({1: 2, 2: 4}, {(1, 2): 1},
                {(1, 0): 0, (1, 1): 0, (1, 2): 1, (2, 0): 0, (2, 1): 1, (2, 2): 0})
    if shape in ("d2c0", "d2c1"):
        delta = 4 if shape == "d2c0" else 5
        return ({1: 2, 2: delta}, {(1, 2): delta},
                {(1, 0): 0, (1, 1): 0, (1, 2): delta, (2, 0): 0, (2, 1): 0, (2, 2): 0})
    raise ValueError(shape)


def unit_count(t, k, shape):
    S, B, C = shape_values(t, k, shape)
    return t * (len(S) + len(B) + len(C))


def encode_shape(t, k, shape):
    """case_b.encode_case_b(t, k) with the values of the shape fixed by unit clauses."""
    cnf, names = cb.encode_case_b(t, k)
    A, Sv, Bv = names[0], names[1], names[2]
    S, B, C = shape_values(t, k, shape)

    def fix(vars_, want):
        for r in range(t):
            cnf.clauses.append([vars_[r]] if (want >> r) & 1 else [-vars_[r]])

    for i, s in S.items():
        fix(Sv[i], s)
    for key, b in B.items():
        fix(Bv[key], b)
    for (i, c), col in C.items():
        fix([A[i][r][c] for r in range(t)], col)
    return cnf, names


def col(A, c, t):
    return sa.mat_apply(A, 1 << c, t)


def in_shape(As, ss, B, t, k, shape):
    """Do the coordinates (As, ss, B) carry the normal form of Lemma 35 and the shape's values?"""
    if not cb.in_normal_form(As, ss, B, t, k):
        return False
    S, Bs, C = shape_values(t, k, shape)
    return (all(ss[i] == s for i, s in S.items()) and all(B[key] == b for key, b in Bs.items())
            and all(col(As[i], c, t) == v for (i, c), v in C.items()))


def accepts(As, ss, B, t, k, shape):
    cnf, names = encode_shape(t, k, shape)
    return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, t, t + k - 1))


# ---------- the systems that U+ carries (k = 3) ----------
# U+ = span(u, n_1, n_2) with values in X_1 = F_2^3, x0 = sigma(u) = e_0, beta(u, U+) = 0 and A_u = 0
# on X_1 (Proposition 26(e), Lemma 26(a)). Element h of U+ = bit mask over (u, n_1, n_2).

def n_systems():
    """Every anisotropic system on U+ as above: (A_1, A_2, s_1, s_2, b). A_i e_0 = 0 and
    A_i s_i = 0 are forced by (*) (h = u, h' = n_i and Lemma 21(b)), so only those A_i are tried."""
    mats = [A for A in range(1 << 9) if sa.mat_apply(A, 1, 3) == 0]
    killing = {s: [A for A in mats if sa.mat_apply(A, s, 3) == 0] for s in range(1, 8)}
    out, tried = [], 0
    for s1, s2, b in itertools.product(range(1, 8), range(1, 8), range(8)):
        for A1, A2 in itertools.product(killing[s1], killing[s2]):
            tried += 1
            at, sv = sa.tables([0, A1, A2], [1, s1, s2], {(0, 1): 0, (0, 2): 0, (1, 2): b}, 3)
            if sa.anisotropic(sv) and sa.is_system(at, sv, 3, 3):
                out.append((A1, A2, s1, s2, b))
    return out, tried


def classify_n(A1, A2, s1, s2, b):
    """'c', 'd1', 'd2' as in Proposition 27 (some basis u, n_1', n_2' of U+), or 'other'."""
    at, sv = sa.tables([0, A1, A2], [1, s1, s2], {(0, 1): 0, (0, 2): 0, (1, 2): b}, 3)
    if b == 0 and A1 == 0 and A2 == 0:
        return "c"
    found = set()
    for p, q in itertools.permutations(range(2, 8), 2):
        if not (p & 6 and q & 6 and (p ^ q) & 6):
            continue
        a, s, bb = sv[p], sv[q], sv[p ^ q] ^ sv[p] ^ sv[q]
        Ap, Aq = at[p], at[q]

        def f(A, x):
            return sa.mat_apply(A, x, 3)

        if (bb == 1 and sa.rank_f2([1, a, s]) == 3 and f(Ap, a) == 0 and f(Ap, s) == 1
                and f(Aq, s) == 0 and f(Aq, a) == 1):
            found.add("d1")
        if (s == bb and sa.rank_f2([1, a, bb]) == 3 and f(Ap, a) == 0 and f(Ap, bb) == bb
                and Aq == 0):
            found.add("d2")
    if len(found) == 1:
        return found.pop()
    return "other"


def n_census():
    systems, tried = n_systems()
    st = {"tried": tried, "systems": len(systems), "c": 0, "d1": 0, "d2": 0, "other": 0}
    for sysv in systems:
        st[classify_n(*sysv)] += 1
    return st


def shape_on_n(shape):
    """The values a shape fixes, read on U+ and X_1 = span(e_0, e_1, e_2): (A_1, A_2, s_1, s_2, b)
    as 3 x 3 data, or None if a fixed column leaves X_1."""
    S, B, C = shape_values(6, 3, shape)
    mats = []
    for i in (1, 2):
        cols = [C[(i, c)] for c in range(3)]
        if any(v >> 3 for v in cols):
            return None
        mats.append(sa.from_cols(cols, 3))
    return mats[0], mats[1], S[1], S[2], B[(1, 2)]


# ---------- selfcheck ----------

def selfcheck():
    census = n_census()
    on_n = {}
    for shape in SHAPES:
        data = shape_on_n(shape)
        at, sv = sa.tables([0, data[0], data[1]], [1, data[2], data[3]],
                           {(0, 1): 0, (0, 2): 0, (1, 2): data[4]}, 3)
        on_n[shape] = {"system": sa.is_system(at, sv, 3, 3) and sa.anisotropic(sv),
                       "class": classify_n(*data)}
    units = {f"{t},{k},{s}": unit_count(t, k, s)
             for t, k, s in ((3, 2, "c"), (4, 2, "c"), (6, 3, "c"), (6, 3, "d1"), (6, 3, "d2c0"),
                             (6, 3, "d2c1"))}
    st = {"census": census, "on_n": on_n, "units": units}
    st["graded"] = {
        "census": {k: census[k] for k in ("systems", "c", "d1", "d2", "other")}
        == {"systems": 192, "c": 24, "d1": 24, "d2": 144, "other": 0},
        "shapes_on_n": all(v["system"] for v in on_n.values())
        and [on_n[s]["class"] for s in SHAPES] == ["c", "d1", "d2", "d2"],
        "units": list(units.values()) == [9, 12, 54, 54, 54, 54]}
    return st


# ---------- solving ----------

def instance_name(t, k, shape):
    return f"sh_t{t}_k{k}_{shape}"


def rank_at(At, t):
    return sa.rank_f2(sa.rows_of(At, t))


def model_facts(As, ss, B, t, k, shape):
    """Facts that the hand results predict for a model (Proposition 26(a), Proposition 27(c4),
    Corollary 20)."""
    d = t + k - 1
    at, sv = sa.tables(As, ss, B, d)
    facts = {"max_rank": max(rank_at(at[h], t) for h in range(1, 1 << d))}
    R = sa.independent([col(As[0], c, t) for c in range(t)])
    X1 = [1 << c for c in range(k)]
    facts["dim_X1_cap_R"] = len(X1) + len(R) - sa.rank_f2(X1 + R)
    if shape.startswith("d2"):
        facts["rank_n2"] = rank_at(at[4], t)
        facts["rank_u_n2"] = rank_at(at[5], t)
    return facts


def child(t, k, shape, solver, path):
    from pysat.solvers import Solver
    cnf, names = encode_shape(t, k, shape)
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
        As, ss, B = sa.decode(s.get_model(), names, t, t + k - 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve(t, k, shape, solver, budget_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    d = t + k - 1
    name = instance_name(t, k, shape)
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--k",
           str(k), "--shape", shape, "--solver", solver, "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": k, "shape": shape, "d": d, "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and in_shape(As, ss, B, t, k, shape))
        res["facts"] = model_facts(As, ss, B, t, k, shape)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


# Pre-registered (m12/predictions.md). SAT counts only with a verified model; UNKNOWN and ERROR are
# reported and not graded.
EXPECTED = {"sh_t3_k2_c": "UNSAT", "sh_t4_k2_c": "UNSAT"}
EXPLORATORY = ("sh_t6_k3_d1", "sh_t6_k3_d2c0", "sh_t6_k3_d2c1", "sh_t6_k3_c")


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("sh_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    for name, want in EXPECTED.items():
        r = results.get(name)
        if r is None or r["status"] not in ("SAT", "UNSAT"):
            ungraded[name] = "missing" if r is None else r["status"]
            continue
        graded[name] = r["status"] == want and (want == "UNSAT" or r["verified"])
    # In a verified model of an exploratory instance, the hand results predict: every rank <= 3
    # (Proposition 26(a)); dim(X_1 n R) >= 2 in shape c (Proposition 27(c4)); rank A_(n_2) <= 2 in
    # shape d2 (Corollary 20(a)); rank A_(u + n_2) <= 2 in shape d2c1 (Corollary 20(b)).
    for name in EXPLORATORY:
        r = results.get(name)
        if r is None or r["status"] != "SAT":
            continue
        graded[name + "_verified"] = bool(r.get("verified"))
        fa = r.get("facts") or {}
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - r["k"]
        if r["shape"] == "c":
            graded[name + "_c4"] = fa.get("dim_X1_cap_R", 0) >= r["k"] - 1
        if r["shape"].startswith("d2"):
            graded[name + "_cor20a"] = fa.get("rank_n2", 99) <= 2
        if r["shape"] == "d2c1":
            graded[name + "_cor20b"] = fa.get("rank_u_n2", 99) <= 2
    explore = {name: {key: results[name].get(key) for key in ("status", "seconds", "vars",
                                                               "clauses", "verified", "facts")}
               for name in EXPLORATORY if name in results}
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    t63 = [results.get(n, {}).get("status") for n in EXPLORATORY]
    return {"graded": graded, "ungraded": ungraded, "exploratory": explore, "times": times,
            "all_four_unsat": t63 == ["UNSAT"] * 4}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=3)
    ap.add_argument("--k", type=int, default=2)
    ap.add_argument("--shape", default="c", choices=SHAPES)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=5.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.k, args.shape, args.solver, args.child_out)
    elif args.part == "solve":
        res = solve(args.t, args.k, args.shape, args.solver, args.budget_minutes * 60,
                    args.out_dir)
        print(f"SUMMARY {res['name']} {res['status']}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {sorted(out['ungraded'])} "
              f"all_four_unsat {out['all_four_unsat']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
