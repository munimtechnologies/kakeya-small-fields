# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m26: the base change inside U+ (Lemma 66, notes/a13.md) on the pairs (M, q) of Lemma 41,
and a runner for what job m25 (a6_r4q.py) leaves at t = 6.

Setting as in shape_c2.py (k = 2, m = t - 2): N = U+ = span(u, v), M = M_v on X/X_1, q = [sigma(w)],
and the type of Lemma 40. Lemma 66: an element n of N whose matrix M_n is invertible is again a
Case B element of rank t - 2 with the same ker A_u, Im A_u, N and W, and the normal form of Lemma 41
taken from n instead of u has the same q (as a vector of X/X_1, in the same basis) and the same
type, with the matrix

    type   base     second    M'
    i      u + v    v         (I + M)^-1 M     when I + M is invertible
    ii     v        u         M^-1             when M is invertible
    iii    v        u + v     M^-1 + I         when M is invertible
    iii    u + v    u         (I + M)^-1       when I + M is invertible

Moving (M', q) back to the chosen representatives by Lemma 39 (M' -> g^-1 M' g, q -> g^-1 q, then
the least q of its C(M)-orbit) gives another pair of Lemma 41. The pairs fall into classes under
these moves, and Case B at (t, 2) exists iff, for one class, one instance of one of its pairs is
satisfiable. Hand counts (a13.md): at t = 6 the 124 pairs of Lemma 65 fall into 102 classes (123
instances instead of 146); at t = 5 the 38 pairs fall into 33 (42 instances instead of 47).

Vectors and m x m matrices are bit masks as in shape_c.py.

Parts: selfcheck (pure Python: the classes against the hand counts, and that every move keeps the
type, lands on a pair of Lemma 41 and is undone by the move back); solve (the pending instances at
t: for every class without a pair whose instances are all UNSAT already, the not-yet-UNSAT
instances of its least pair; each in a child process with a time budget, under a group budget;
needs python-sat); grade (m26/predictions.md).

Usage: python a6_r4s.py --part selfcheck|solve|grade [--t 6] [--unsat q2_t6_i03,q2_t6_i07,...]
                        [--budget-minutes 10] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import functools
import json
import os
import subprocess
import sys
import time

import case_b_shapes as cs
import sat_aniso as sa
import shape_c as sc
import shape_c2 as s2

T = 6
CONTROLS = (3, 4)

# Hand counts of a13.md: pairs (M, q) of Lemma 41 (M = 0 and M = I left out at t = 6 only), moves
# of Lemma 66 (one per pair and per applicable row of the table), classes, instances of the least
# pairs, classes by type, and classes by size.
HAND = {
    3: {"pairs": 2, "moves": 2, "classes": 2, "instances": 3,
        "by_type": {"i": 1, "ii": 1}, "sizes": {"1": 2}},
    4: {"pairs": 10, "moves": 8, "classes": 9, "instances": 12,
        "by_type": {"i": 3, "ii": 3, "iii": 3}, "sizes": {"1": 8, "2": 1}},
    5: {"pairs": 38, "moves": 24, "classes": 33, "instances": 42,
        "by_type": {"i": 9, "ii": 9, "iii": 15}, "sizes": {"1": 28, "2": 5}},
    6: {"pairs": 124, "moves": 68, "classes": 102, "instances": 123,
        "by_type": {"i": 21, "ii": 21, "iii": 60}, "sizes": {"1": 81, "2": 20, "3": 1}},
}


# ---------- the instances of Lemma 41 that a6_r4q.py runs ----------

def todo(t):
    """[(shape_c2 index, (M, q, type, c))] at t; M = 0 and M = I are left out at t = 6
    (Corollary 36), as in a6_r4q.todo."""
    ident = sc.identity(t - 2)
    return [(idx, inst) for idx, inst in enumerate(s2.instances(t))
            if t < 6 or inst[0] not in (0, ident)]


def by_pair(t):
    """{(M, q): [(idx, inst), ...]} over todo(t), in instance order."""
    out = {}
    for idx, inst in todo(t):
        out.setdefault((inst[0], inst[1]), []).append((idx, inst))
    return out


def round_robin(items):
    """Interleave by M, as a6_r4q.round_robin does."""
    groups = {}
    for item in items:
        groups.setdefault(item[1][0], []).append(item)
    groups = list(groups.values())
    out = []
    for r in range(max((len(g) for g in groups), default=0)):
        out.extend(g[r] for g in groups if r < len(g))
    return out


# ---------- Lemma 66 ----------

def invertible(M, m):
    return sa.rank_f2(sa.rows_of(M, m)) == m


def moves(M, q, typ, m):
    """The pairs (M', q) that Lemma 66 gives from (M, q) of the given type: 0, 1 or 2 of them."""
    ident = sc.identity(m)
    out = []
    if typ != "i" and invertible(M, m):
        Mi = sa.mat_inv(M, m)
        out.append(Mi if typ == "ii" else Mi ^ ident)
    if typ != "ii" and invertible(M ^ ident, m):
        Ni = sa.mat_inv(M ^ ident, m)
        out.append(sa.mat_mul(Ni, M, m) if typ == "i" else Ni)
    return [(Mp, q) for Mp in out]


@functools.lru_cache(maxsize=None)
def transporters(m):
    """{A: g} with g^-1 A g = the least matrix of the similarity class of A (shape_c.orbits)."""
    out = {}
    group = [(g, sa.mat_inv(g, m)) for g in sc.gl(m)]
    for (rep,), _, _ in sc.orbits(m, 1):
        for g, gi in group:
            out.setdefault(sa.mat_mul(sa.mat_mul(g, rep, m), gi, m), g)
    return out


def canonical(Mp, qp, m):
    """The pair of Lemma 41 (least M of its class, least q of its C(M)-orbit) that (Mp, qp) is
    moved to by Lemma 39: M -> g^-1 M g, q -> g^-1 q."""
    g = transporters(m)[Mp]
    gi = sa.mat_inv(g, m)
    rep = sa.mat_mul(sa.mat_mul(gi, Mp, m), g, m)
    q2 = sa.mat_apply(gi, qp, m)
    least = min(sa.mat_apply(h, q2, m) for h in s2.centraliser(rep, m))
    return rep, least


def _find(parent, i):
    while parent[i] != i:
        parent[i] = parent[parent[i]]
        i = parent[i]
    return i


@functools.lru_cache(maxsize=None)
def analysis(t):
    """The pairs of todo(t), the moves of Lemma 66 between them, and their classes."""
    m = t - 2
    ident = sc.identity(m)
    pairs = []
    for _, (M, q, typ, c) in todo(t):
        if not pairs or pairs[-1][:2] != (M, q):
            pairs.append((M, q, typ))
    index = {(M, q): i for i, (M, q, typ) in enumerate(pairs)}
    parent = list(range(len(pairs)))
    checks = {"type_kept": True, "not_0_or_I": True, "lands_on_pair": True,
              "same_class_moves_fixed": True, "moves_undone": True}
    edges = []
    for i, (M, q, typ) in enumerate(pairs):
        for Mp, qp in moves(M, q, typ, m):
            if t == 6 and Mp in (0, ident):
                checks["not_0_or_I"] = False
                continue
            if s2.lemma40_type(Mp, qp, m) != typ:
                checks["type_kept"] = False
            rep, least = canonical(Mp, qp, m)
            j = index.get((rep, least))
            if j is None:
                checks["lands_on_pair"] = False
                continue
            if pairs[j][2] != typ:
                checks["type_kept"] = False
            if rep == M and j != i:
                checks["same_class_moves_fixed"] = False
            edges.append((i, j))
            ri, rj = _find(parent, i), _find(parent, j)
            if ri != rj:
                parent[max(ri, rj)] = min(ri, rj)
    edge_set = set(edges)
    checks["moves_undone"] = all((j, i) in edge_set for i, j in edge_set)
    groups = {}
    for i in range(len(pairs)):
        groups.setdefault(_find(parent, i), []).append(i)
    classes = sorted(sorted(g) for g in groups.values())
    reps = [pairs[g[0]] for g in classes]
    by_type = {}
    for M, q, typ in reps:
        by_type[typ] = by_type.get(typ, 0) + 1
    sizes = {}
    for g in classes:
        sizes[str(len(g))] = sizes.get(str(len(g)), 0) + 1
    rep_pairs = {(M, q) for M, q, typ in reps}
    instances = sum(len(v) for pq, v in by_pair(t).items() if pq in rep_pairs)
    counts = {"pairs": len(pairs), "moves": len(edges), "classes": len(classes),
              "instances": instances, "by_type": by_type, "sizes": sizes}
    return {"t": t, "counts": counts, "checks": checks, "pairs": pairs, "classes": classes,
            "reps": reps, "edges": sorted(edge_set),
            "hand": HAND.get(t), "graded": all(checks.values()) and counts == HAND.get(t)}


def representatives(t):
    """[(idx, inst)] of todo(t) whose pair is the least pair of its class."""
    rep_pairs = {(M, q) for M, q, typ in analysis(t)["reps"]}
    return [(idx, inst) for idx, inst in todo(t) if (inst[0], inst[1]) in rep_pairs]


def class_of_instance(t):
    """{instance name: class number} over todo(t)."""
    an = analysis(t)
    pair_class = {}
    for n, g in enumerate(an["classes"]):
        for i in g:
            pair_class[an["pairs"][i][:2]] = n
    return {s2.instance_name(t, idx): pair_class[(inst[0], inst[1])] for idx, inst in todo(t)}


def pending(t, unsat_names):
    """The instances still to run at t, given the names already UNSAT (from job m25): for every
    class without a pair whose instances are all UNSAT, the instances of its least pair that are
    not UNSAT yet."""
    an = analysis(t)
    pairs = by_pair(t)
    unsat = set(unsat_names)
    refuted = {pq for pq, lst in pairs.items()
               if all(s2.instance_name(t, idx) in unsat for idx, _ in lst)}
    out = []
    for g in an["classes"]:
        members = [an["pairs"][i][:2] for i in g]
        if any(pq in refuted for pq in members):
            continue
        out.extend((idx, inst) for idx, inst in pairs[members[0]]
                   if s2.instance_name(t, idx) not in unsat)
    return out


# ---------- selfcheck ----------

def selfcheck():
    st = {}
    for t in (3, 4, 5, 6):
        an = analysis(t)
        st[str(t)] = {"counts": an["counts"], "checks": an["checks"], "hand": an["hand"],
                      "graded": an["graded"]}
    st["pending_6_none_unsat"] = len(pending(6, []))
    st["graded"] = {str(t): st[str(t)]["graded"] for t in (3, 4, 5, 6)}
    st["graded"]["pending"] = st["pending_6_none_unsat"] == HAND[6]["instances"]
    return st


# ---------- solving (as in a6_r4q.py, through shape_c2.encode_q) ----------

def child(t, inst, solver, path):
    from pysat.solvers import Solver
    M, q, typ, c = inst
    cnf, names = s2.encode_q(t, M, q, typ, c)
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
        As, ss, B = sa.decode(s.get_model(), names, t, t + 1)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def child_cmd(t, inst, solver, path):
    M, q, typ, c = inst
    return [sys.executable, os.path.abspath(__file__), "--part", "child", "--t", str(t),
            "--inst", json.dumps([M, q, typ, c]), "--solver", solver, "--child-out", path]


def solve_one(t, idx, inst, solver, budget_seconds, out_dir):
    d = t + 1
    M, q, typ, c = inst
    name = s2.instance_name(t, idx)
    path = os.path.join(out_dir, name + ".child.json")
    start = time.time()
    try:
        subprocess.run(child_cmd(t, inst, solver, path), timeout=budget_seconds, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    res.update({"t": t, "k": 2, "d": d, "idx": idx, "M": M, "q": q, "type": typ, "c": c,
                "name": name, "wall_seconds": round(time.time() - start, 2)})
    if res["status"] == "SAT":
        As, ss = res["A"], res["s"]
        B = {(i, j): v for i, j, v in res["B"]}
        at, sv = sa.tables(As, ss, B, d)
        res["verified"] = (sa.is_system(at, sv, d, t) and sa.anisotropic(sv)
                           and cs.in_shape(As, ss, B, t, 2, "c")
                           and sc.satisfies_split(As, t, 2, (M,))
                           and s2.satisfies_q(As, ss, B, t, M, q, typ, c))
        res["facts"] = sc.model_facts(As, ss, B, t, 2)
    with open(os.path.join(out_dir, name + ".json"), "w") as f:
        json.dump(res, f, indent=1)
    print(f"solve {name}: {json.dumps(res, sort_keys=True)}", flush=True)
    return res


def run(t, items, budget_seconds, group_seconds, out_dir):
    os.makedirs(out_dir, exist_ok=True)
    start = time.time()
    counts = {}
    for idx, inst in items:
        left = group_seconds - (time.time() - start)
        if left < 1:
            M, q, typ, c = inst
            res = {"status": "SKIPPED", "t": t, "idx": idx, "M": M, "q": q, "type": typ, "c": c,
                   "name": s2.instance_name(t, idx)}
            with open(os.path.join(out_dir, res["name"] + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            res = solve_one(t, idx, inst, "auto", min(budget_seconds, left), out_dir)
        counts[res["status"]] = counts.get(res["status"], 0) + 1
    return counts


# ---------- grading ----------

def load_results(out_dir):
    results = {}
    for fn in sorted(os.listdir(out_dir)):
        if fn.startswith("q2_") and fn.endswith(".json") and not fn.endswith(".child.json"):
            with open(os.path.join(out_dir, fn)) as f:
                r = json.load(f)
            results[r["name"]] = r
    return results


# Pre-registered (m26/predictions.md). Graded: the selfcheck; every decided control instance
# (t = 3, 4) UNSAT; every SAT answer verified with ranks <= t - 2, Lemma 38's facts and dim D >= 1.
# Instances at t = 6 are exploratory.
def grade(out_dir, unsat_names=()):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "selfcheck.json")) as f:
            graded["selfcheck"] = all(json.load(f)["graded"].values())
    except (OSError, ValueError, KeyError):
        ungraded["selfcheck"] = "missing"
    results = load_results(out_dir)
    status = {}
    for t in CONTROLS:
        status[str(t)] = {s2.instance_name(t, idx): results.get(s2.instance_name(t, idx), {})
                          .get("status", "missing") for idx, _ in representatives(t)}
        for name, s in status[str(t)].items():
            if s in ("SAT", "UNSAT"):
                graded[name] = s == "UNSAT"
            else:
                ungraded[name] = s
    status["6"] = {s2.instance_name(T, idx): results.get(s2.instance_name(T, idx), {})
                   .get("status", "missing") for idx, _ in pending(T, unsat_names)}
    for name, r in results.items():
        if r.get("status") != "SAT":
            continue
        fa = r.get("facts") or {}
        graded[name + "_verified"] = bool(r.get("verified"))
        graded[name + "_ranks"] = fa.get("max_rank", 99) <= r["t"] - 2
        graded[name + "_lemma38"] = all(fa.get(key) for key in
                                        ("T_ok", "M_u_is_I", "commute", "lemma38d", "lemma38e"))
        graded[name + "_d"] = fa.get("dim_D", 0) >= 1
    counts = {t: {s: list(v.values()).count(s) for s in sorted(set(v.values()))}
              for t, v in status.items()}
    # Classes at t = 6 refuted after this job: a pair with every instance UNSAT (here or in the
    # names given).
    unsat = set(unsat_names) | {n for n, r in results.items()
                                if r.get("t") == T and r.get("status") == "UNSAT"}
    an = analysis(T)
    pairs = by_pair(T)
    refuted_pairs = {pq for pq, lst in pairs.items()
                     if all(s2.instance_name(T, idx) in unsat for idx, _ in lst)}
    refuted_classes = sum(1 for g in an["classes"]
                          if any(an["pairs"][i][:2] in refuted_pairs for i in g))
    times = {n: r.get("wall_seconds") for n, r in results.items()}
    six = list(status["6"].values())
    return {"graded": graded, "ungraded": ungraded, "counts": counts, "times": times,
            "decided_6": sorted(n for n, s in status["6"].items() if s in ("SAT", "UNSAT")),
            "refuted_classes_6": refuted_classes, "classes_6": len(an["classes"]),
            "all_unsat_6": bool(six) and all(s == "UNSAT" for s in six),
            "any_sat_6": any(s == "SAT" for s in six)}


def parse_names(text):
    return [x for x in text.split(",") if x]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "child", "grade"],
                    default="selfcheck")
    ap.add_argument("--t", type=int, default=T)
    ap.add_argument("--inst", default="[]")
    ap.add_argument("--unsat", default="", help="instance names already UNSAT (job m25)")
    ap.add_argument("--solver", default="auto")
    ap.add_argument("--budget-minutes", type=float, default=10.0)
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        M, q, typ, c = json.loads(args.inst)
        child(args.t, (M, q, typ, c), args.solver, args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "selfcheck":
        st = selfcheck()
        print(f"selfcheck: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "selfcheck.json"), "w") as f:
            json.dump(st, f, indent=1)
        with open(os.path.join(args.out_dir, "classes_6.json"), "w") as f:
            an = analysis(6)
            json.dump({"pairs": an["pairs"], "classes": an["classes"], "edges": an["edges"],
                       "class_of_instance": class_of_instance(6),
                       "representatives": [s2.instance_name(6, idx)
                                           for idx, _ in representatives(6)]}, f, indent=1)
    elif args.part == "controls":
        for t in CONTROLS:
            counts = run(t, representatives(t), 120, 600, args.out_dir)
            print(f"SUMMARY control t{t} {json.dumps(counts, sort_keys=True)}", flush=True)
    elif args.part == "solve":
        items = round_robin(pending(args.t, parse_names(args.unsat)))
        print(f"pending t{args.t}: {len(items)} instances", flush=True)
        counts = run(args.t, items, args.budget_minutes * 60, args.group_minutes * 60,
                     args.out_dir)
        print(f"SUMMARY solve t{args.t} {json.dumps(counts, sort_keys=True)}", flush=True)
    else:
        out = grade(args.out_dir, parse_names(args.unsat))
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"counts {json.dumps(out['counts'], sort_keys=True)} "
              f"refuted_classes_6 {out['refuted_classes_6']}/{out['classes_6']}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)


if __name__ == "__main__":
    main()
