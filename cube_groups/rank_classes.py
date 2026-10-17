# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""The SAT search of sat_aniso.py, split by the similarity class of one element.

Setting and encoding as in sat_aniso.py. Take an anisotropic system with dim X = t, dim V = d and
any u != 0 in V. Choose a basis of V with e_1 = u. A change of basis g of X (which acts on systems)
makes A_(e_1) = g A_u g^-1 a fixed representative C of the similarity class of A_u. Then
s_1 = sigma(e_1) lies in ker C (Lemma 21(b)), and an invertible z commuting with C keeps
A_(e_1) = C and moves s_1 to z s_1, so s_1 may be taken to be the least vector of its orbit. So:

    an anisotropic system (t, d) with an element similar to C exists  iff  one of the SAT calls
    (A_(e_1) = C, s_1 = r), r an orbit representative in ker C \\ {0}, is satisfiable.

For C = 0 the whole of GL(X) commutes with C, and the echelon form of sat_aniso.py is used instead.
Every A_h of an anisotropic system is singular (A_h sigma(h) = 0 with sigma(h) != 0), so the calls
for every singular class together decide whether A(t) >= d, without any lemma of the notes. The
calls for the classes of one rank test Lemma 30 (rank t - 1 gives dim V <= t) and the rank-3
question of notes/rank-restriction.md.

Classes come from rational canonical forms. A class of t x t matrices over F_2 is a choice of a
partition lambda_p for each irreducible polynomial p, with sum of deg(p) |lambda_p| equal to t; its
representative is block-diagonal, with the companion matrix of p^m for each part m of lambda_p. Its
rank is t minus the number of parts of lambda_x. The selfcheck compares this list with the orbits of
GL(n, F_2) on all n x n matrices, found by brute force, for n <= 4.

Polynomials over F_2 are int bitmasks (bit i = coefficient of x^i); vectors and matrices are as in
sat_aniso.py.

Usage: python rank_classes.py --part selfcheck|solve|grade [--t T --d D --ranks 3,4]
                              [--budget-minutes 5] [--total-minutes 60] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import subprocess
import sys
import time

import sat_aniso as sa

X_POLY = 0b10


# ---------- polynomials over F_2 ----------

def pdeg(p):
    return p.bit_length() - 1


def pmod(a, b):
    db = pdeg(b)
    while a and pdeg(a) >= db:
        a ^= b << (pdeg(a) - db)
    return a


def pmul(a, b):
    out = 0
    while b:
        if b & 1:
            out ^= a
        a <<= 1
        b >>= 1
    return out


def irreducibles(n):
    """The irreducible polynomials of degree 1..n, in increasing order as integers."""
    out = []
    for p in range(2, 1 << (n + 1)):
        if all(pmod(p, q) for q in out if 2 * pdeg(q) <= pdeg(p)):
            out.append(p)
    return out


def partitions(n, maxpart=None):
    if maxpart is None:
        maxpart = n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


# ---------- similarity classes ----------

def companion(p, off):
    """Cells of the companion matrix of p, with its top-left corner at (off, off)."""
    k = pdeg(p)
    cells = [(off + i + 1, off + i) for i in range(k - 1)]
    return cells + [(off + r, off + k - 1) for r in range(k) if (p >> r) & 1]


def classes(n):
    """Every similarity class of n x n matrices over F_2, as dicts with the representative C, its
    rank, and the invariant [[p, lambda_p], ...]."""
    irr = irreducibles(n)
    invs = []

    def rec(idx, left, chosen):
        if left == 0:
            invs.append(list(chosen))
            return
        if idx == len(irr):
            return
        p = irr[idx]
        k = pdeg(p)
        rec(idx + 1, left, chosen)
        for size in range(1, left // k + 1):
            for lam in partitions(size):
                rec(idx + 1, left - k * size, chosen + [(p, lam)])

    rec(0, n, [])
    out = []
    for inv in invs:
        cells, off = [], 0
        for p, lam in inv:
            for m in lam:
                q = 1
                for _ in range(m):
                    q = pmul(q, p)
                cells += companion(q, off)
                off += pdeg(q)
        C = sa.entries(n, cells)
        out.append({"C": C, "rank": sa.rank_f2(sa.rows_of(C, n)),
                    "inv": [[p, list(lam)] for p, lam in inv]})
    return out


def rank_counts(n):
    out = {}
    for c in classes(n):
        out[c["rank"]] = out.get(c["rank"], 0) + 1
    return out


def conj_transvection(M, n, i, j):
    """T M T^-1 for T = I + E_ij (i != j, T^-1 = T): add row j to row i, then column i to
    column j."""
    rows = sa.rows_of(M, n)
    rows[i] ^= rows[j]
    return sa.from_rows([row ^ (1 << j) if (row >> i) & 1 else row for row in rows], n)


def brute_orbits(n):
    """Orbit labels of GL(n, F_2) acting by conjugation on all n x n matrices, by union-find over the
    transvections I + E_ij, which generate GL(n, F_2) = SL(n, F_2)."""
    parent = list(range(1 << (n * n)))

    def find(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for M in range(1 << (n * n)):
        for i in range(n):
            for j in range(n):
                if i != j:
                    a, b = find(M), find(conj_transvection(M, n, i, j))
                    if a != b:
                        parent[a] = b
    return [find(M) for M in range(1 << (n * n))]


def check_classes(n):
    """Do the representatives lie in distinct orbits, one in each?"""
    labels = brute_orbits(n)
    reps = classes(n)
    orbits = len(set(labels))
    hit = len({labels[c["C"]] for c in reps})
    return {"n": n, "classes": len(reps), "orbits": orbits, "distinct": hit,
            "agree": len(reps) == orbits == hit}


def gl(t):
    return [g for g in range(1 << (t * t)) if sa.rank_f2(sa.rows_of(g, t)) == t]


def centraliser_units(C, t, limit=18):
    """The invertible matrices commuting with C, or None if the centraliser algebra has dimension
    above limit."""
    cons = []
    for r in range(t):
        for c in range(t):
            m = 0
            for k in range(t):
                if (C >> (t * k + c)) & 1:          # (g C)_rc has g_rk C_kc
                    m ^= 1 << (t * r + k)
                if (C >> (t * r + k)) & 1:          # (C g)_rc has C_rk g_kc
                    m ^= 1 << (t * k + c)
            cons.append(m)
    basis = sa.nullspace(cons, t * t)
    if len(basis) > limit:
        return None
    units = []
    for c in range(1 << len(basis)):
        g = sa.combine(basis, c)
        if sa.rank_f2(sa.rows_of(g, t)) == t:
            units.append(g)
    return units


def kernel_reps(C, t, units):
    """The least vector of each orbit of units on ker C \\ {0} (every vector if units is None)."""
    ker = [x for x in range(1, 1 << t) if sa.mat_apply(C, x, t) == 0]
    if units is None:
        return ker
    reps, seen = [], set()
    for x in ker:
        if x not in seen:
            reps.append(x)
            seen.update(sa.mat_apply(g, x, t) for g in units)
    return reps


def instances(t, ranks):
    """(class index, C, s_1) for every class of a rank in ranks and every orbit representative s_1
    (s_1 = None for C = 0, which uses echelon form)."""
    out = []
    for k, cl in enumerate(classes(t)):
        if cl["rank"] not in ranks:
            continue
        C = cl["C"]
        if C == 0:
            out.append((k, C, None))
            continue
        for x in kernel_reps(C, t, centraliser_units(C, t)):
            out.append((k, C, x))
    return out


def encode_class(t, d, C, s1):
    """sat_aniso.encode with A_(e_1) = C and s_1 fixed (echelon form instead when C = 0)."""
    cnf, names = sa.encode(t, d, echelon=C == 0)
    A, S = names[0], names[1]
    for r in range(t):
        for c in range(t):
            v = A[0][r][c]
            cnf.clauses.append([v if (C >> (t * r + c)) & 1 else -v])
        if s1 is not None:
            v = S[0][r]
            cnf.clauses.append([v if (s1 >> r) & 1 else -v])
    return cnf, names


# ---------- soundness check of the normalisation ----------

def moved(g, As, ss, B, t):
    gi = sa.mat_inv(g, t)
    return ([sa.mat_mul(sa.mat_mul(g, A, t), gi, t) for A in As], [sa.mat_apply(g, s, t) for s in ss],
            {k: sa.mat_apply(g, v, t) for k, v in B.items()})


def normalised(As, ss, B, t, cls, group):
    """(k, s_1, As', ss', B'): the system moved by GL(X), found by brute force over group, so that
    A'_1 is the representative C_k of its class and s'_1 the representative of its orbit, as in
    instances(). s_1 is None for C_k = 0 (echelon form), and also when s'_1 is not in ker C_k,
    which happens only for pairs that are not systems."""
    for k, cl in enumerate(cls):
        C = cl["C"]
        g = next((g for g in group if sa.mat_mul(g, As[0], t) == sa.mat_mul(C, g, t)), None)
        if g is not None:
            break
    As, ss, B = moved(g, As, ss, B, t)
    if C == 0:
        return (k, None) + sa.normalize(As, ss, B, t)
    if sa.mat_apply(C, ss[0], t):
        return (k, None, As, ss, B)
    units = centraliser_units(C, t)
    rep = min(sa.mat_apply(z, ss[0], t) for z in units)
    z = next(z for z in units if sa.mat_apply(z, ss[0], t) == rep)
    return (k, rep) + moved(z, As, ss, B, t)


def accepts(C, s1, As, ss, B, t, d):
    cnf, names = encode_class(t, d, C, s1)
    return sa.satisfies(cnf, sa.assignment(cnf, names, As, ss, B, t, d))


def normalisation_check(rng, count):
    """On random systems, restrictions and one-bit mutations (sat_aniso.random_examples, t <= 3):
    after normalisation, the class CNF accepts exactly the anisotropic systems."""
    st = {"cases": 0, "accepted": 0, "disagree": 0, "classes_hit": 0}
    cache, hit = {}, set()
    for t, d, As, ss, B in sa.random_examples(rng, count):
        if t not in cache:
            cache[t] = (classes(t), gl(t))
        cls, group = cache[t]
        at, sv = sa.tables(As, ss, B, d)
        good = sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
        k, s1, nAs, nss, nB = normalised(As, ss, B, t, cls, group)
        acc = accepts(cls[k]["C"], s1, nAs, nss, nB, t, d)
        st["cases"] += 1
        st["accepted"] += acc
        st["disagree"] += acc != good
        hit.add((t, k))
    st["classes_hit"] = len(hit)
    return st


def selfcheck(rng):
    st = {"counts": {n: [len(classes(n)), sum(c["rank"] < n for c in classes(n))]
                     for n in range(1, 6)},
          "rank_counts_5": rank_counts(5), "rank3_6": rank_counts(6).get(3, 0),
          "brute": [check_classes(n) for n in range(1, 5)],
          "normalisation": normalisation_check(rng, 120),
          "instances": {"t4_r0123": len(instances(4, (0, 1, 2, 3))),
                        "t5_r4": len(instances(5, (4,))), "t5_r3": len(instances(5, (3,))),
                        "t5_r012": len(instances(5, (0, 1, 2)))},
          "classes_5": [c for c in classes(5) if c["rank"] < 5]}
    norm = st["normalisation"]
    st["graded"] = {
        "counts": st["counts"] == {1: [2, 1], 2: [6, 3], 3: [14, 8], 4: [34, 20], 5: [74, 47]},
        "rank_counts_5": st["rank_counts_5"] == {0: 1, 1: 2, 2: 6, 3: 13, 4: 25, 5: 27},
        "rank3_6": st["rank3_6"] == 14,
        "brute_agree": all(b["agree"] for b in st["brute"]),
        "normalisation_agree": norm["disagree"] == 0,
        "nontrivial": 0 < norm["accepted"] < norm["cases"]}
    return st


# ---------- solving ----------

def child(t, d, k, s1, solver, path):
    from pysat.solvers import Solver
    C = classes(t)[k]["C"]
    cnf, names = encode_class(t, d, C, s1)
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


def solve_one(t, d, k, C, s1, rank, solver, budget_seconds, out_dir):
    name = f"t{t}_d{d}_c{k}_s{0 if s1 is None else s1}"
    path = os.path.join(out_dir, name + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t), "--d",
           str(d), "--cls", str(k), "--s1", str(-1 if s1 is None else s1), "--solver", solver,
           "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "d": d, "cls": k, "C": C, "s1": s1, "rank": rank, "name": name,
                "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv) and As[0] == C
                           and (s1 is None or ss[0] == s1))
        res["ranks"] = sorted(sa.rank_f2(sa.rows_of(at[h], t)) for h in range(1, 1 << d))
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def group_key(t, d, ranks):
    return f"t{t}_d{d}_r" + "".join(str(r) for r in sorted(ranks))


def solve_group(t, d, ranks, solver, budget_seconds, total_seconds, out_dir):
    """Every instance of the classes of the given ranks, each with its own budget, until the total
    budget is spent; the rest are recorded as SKIPPED."""
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    cls = classes(t)
    results = []
    for k, C, s1 in instances(t, ranks):
        left = total_seconds - (time.time() - start)
        if left < 5:
            results.append({"status": "SKIPPED", "cls": k, "C": C, "s1": s1,
                            "rank": cls[k]["rank"],
                            "name": f"t{t}_d{d}_c{k}_s{0 if s1 is None else s1}"})
            continue
        results.append(solve_one(t, d, k, C, s1, cls[k]["rank"], solver,
                                 min(budget_seconds, left), out_dir))
    counts = {}
    for r in results:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    key = group_key(t, d, ranks)
    group = {"key": key, "t": t, "d": d, "ranks": sorted(ranks), "counts": counts,
             "seconds": round(time.time() - start, 2), "results": results}
    with open(os.path.join(out_dir, "group_" + key + ".json"), "w") as f:
        json.dump(group, f, indent=1)
    return group


# Pre-registered (notes/predictions.md of run 57). Per instance: SAT counts only with a verified
# model; UNKNOWN, ERROR and SKIPPED are reported and not graded.
EXPECTED_GROUPS = {"t3_d3_r0": "SAT", "t5_d5_r0": "SAT", "t4_d5_r0123": "UNSAT",
                   "t5_d6_r4": "UNSAT"}
EXPLORATORY_GROUPS = ("t5_d6_r3", "t5_d6_r012", "t6_d8_r3")


def grade(out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    groups = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("group_") and fn.endswith(".json"):
            with open(os.path.join(out_dir, fn)) as f:
                g = json.load(f)
            groups[g["key"]] = g
    for key, want in EXPECTED_GROUPS.items():
        if key not in groups:
            ungraded[key] = "missing"
            continue
        for r in groups[key]["results"]:
            if r["status"] not in ("SAT", "UNSAT"):
                ungraded[r["name"]] = r["status"]
                continue
            graded[r["name"]] = r["status"] == want and (want == "UNSAT" or r["verified"])
    # Remark after Proposition 24: a system with t = 5 and dim V = 6 has every rank <= 3, some 3.
    for key, g in groups.items():
        if key.startswith("t5_d6"):
            for r in g["results"]:
                if r["status"] == "SAT":
                    graded[r["name"] + "_verified"] = bool(r.get("verified"))
                    graded[r["name"] + "_ranks"] = max(r.get("ranks") or [0]) == 3
    explore = {key: {"counts": groups[key]["counts"], "seconds": groups[key]["seconds"],
                     "sat": [r["name"] for r in groups[key]["results"] if r["status"] == "SAT"]}
               for key in EXPLORATORY_GROUPS if key in groups}
    times = {r["name"]: r.get("wall_seconds") for g in groups.values() for r in g["results"]}
    return {"graded": graded, "ungraded": ungraded, "exploratory": explore, "times": times}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "solve", "child", "grade"], default="selfcheck")
    ap.add_argument("--t", type=int, default=4)
    ap.add_argument("--d", type=int, default=5)
    ap.add_argument("--ranks", default="0,1,2,3")
    ap.add_argument("--cls", type=int, default=0)
    ap.add_argument("--s1", type=int, default=-1)
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=5.0)
    ap.add_argument("--total-minutes", type=float, default=60.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(args.t, args.d, args.cls, None if args.s1 < 0 else args.s1, args.solver,
              args.child_out)
    elif args.part == "solve":
        ranks = tuple(int(r) for r in args.ranks.split(","))
        g = solve_group(args.t, args.d, ranks, args.solver, args.budget_minutes * 60,
                        args.total_minutes * 60, args.out_dir)
        print(f"SUMMARY {g['key']} {json.dumps(g['counts'], sort_keys=True)}", flush=True)
    elif args.part == "grade":
        out = grade(args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = selfcheck(random.Random(57))
        print(f"selfcheck: {json.dumps({k: v for k, v in st.items() if k != 'classes_5'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        os.makedirs(args.out_dir, exist_ok=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
