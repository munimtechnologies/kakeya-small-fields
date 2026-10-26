# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m109: where in the system (*) the contradiction "normal form + M" lives, by basis index of V,
by row of X and by group of equations, in the ten core and k = 6 cases of the rank-0 case of
(B7)_8 (t = 8, dim V = 11) (notes/a101.md, cube_groups/m109-predictions.md).

What came back on 2026-10-25 (jobs m108g and m108h, notes/a101.md): every graded check held. With
the normal form and M kept, the deletion-minimal sets of the 16 groups of (*) are large (7 to 11
groups) but nearly the same in all ten cases: Q_vhh, Q_uhh, Q_uvh, L_hv, L_vh, L_hu, L_uh (and
L_vu in eight); Q_hhh is never needed. "M only" is UNSAT in all twelve other k = 6 cases tried.

The system (*) in coordinates (sat_aniso.coeff_ok), for basis indices i, j, k of V and each row r
of X (t = 8 rows):

    (L)  A_j s_i = b(i, j) + A_i b(i, j)                  (b(i, i) = 0: A_i s_i = 0)
    (Q)  A_j b(i, k) + A_i b(k, j) + A_k b(i, j) = 0       (i < k, j not in {i, k})

An equation is kept when its group is kept, all its indices are kept and its row is kept. With
everything kept, encode_sub is m108.encode_star (so sat_aniso.encode) clause for clause. Three
deletion passes per item, each keeping the CNF UNSAT: the indices (IDX_DROP: h_1..h_4, then
h_5..h_7, v_1, v_3, v_2, u), then the rows (ROW_DROP), then the groups that still have an equation
(m108.STAR_DROP). Answers are cached on the equations they keep, so no CNF is solved twice.

Parts:

    check    encode_sub with everything against m108.encode_star and sat_aniso.encode (hash); the
             equation counts of a sub-system by hand; the items of this shard
    reduce   a positive control, then the three passes for each item of this shard (120 s per
             solve)
    grade    the graded checks of m109-predictions.md

Usage: python m109.py --part check|reduce|grade --shard g|h|i|j [--cap-seconds S] [--minutes M]
       [--out-dir D]
"""
import argparse
import itertools
import json
import os
import subprocess
import sys
import time

import m42
import m100
import m102
import m103
import m104
import m106
import m108
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
STAR, STAR_DROP, KIND = m108.STAR, m108.STAR_DROP, m108.KIND
ALL_IDX = tuple(range(D))
ALL_ROWS = tuple(range(T))
# drop h_1..h_4 (phi into X_1) first, then h_5..h_7 (phi onto Q), then v_1, then v_3, v_2 (the
# maps of M), u last
IDX_DROP = (4, 5, 6, 7, 8, 9, 10, 1, 3, 2, 0)
ROW_DROP = (0, 1, 2, 3, 4, 5, 6, 7)
# the six core cases (m106.min_items order) in shards g, h; the four k = 6 cases in i, j
SHARDS = {"g": (0, 1, 2), "h": (3, 4, 5), "i": (6, 7), "j": (8, 9)}
# by hand: indices u, v_2, v_3, h_5, h_6, h_7 (n_u = 1, n_v = 2, n_h = 3) and rows 5, 6, 7:
# (L) n_a * n_b * 3; (Q) each 3-set of the 20 three times (once per j), 3 rows
SUB_IDX, SUB_ROWS = (0, 2, 3, 8, 9, 10), (5, 6, 7)
SUB_COUNTS = {"L_uu": 3, "L_uv": 6, "L_uh": 9, "L_vu": 6, "L_vv": 12, "L_vh": 18, "L_hu": 9,
              "L_hv": 18, "L_hh": 27, "Q_uvv": 9, "Q_uvh": 54, "Q_uhh": 27, "Q_vvv": 0,
              "Q_vvh": 27, "Q_vhh": 54, "Q_hhh": 9}


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the sub-systems of (*) ----------

def equations(d=D):
    """[(group, indices)]: the equations of (*) (one per row), in encode_star's order."""
    out = [(m108.l_group(i, j), (i, j)) for i in range(d) for j in range(d)]
    for i, k in itertools.combinations(range(d), 2):
        out += [(m108.q_group(i, k, j), (i, k, j)) for j in range(d) if j not in (i, k)]
    return out


def count_sub(t, d, groups, idx, rows):
    """{group: number of kept equations} for the groups given."""
    idx, n = set(idx), {g: 0 for g in STAR if g in groups}
    for g, ix in equations(d):
        if g in n and set(ix) <= idx:
            n[g] += len([r for r in rows if r < t])
    return n


def live_groups(groups, idx, rows, t=T, d=D):
    """The groups (in the given order) that keep at least one equation."""
    n = count_sub(t, d, groups, idx, rows)
    return [g for g in groups if n.get(g)]


def encode_sub(t, d, groups, idx, rows):
    """m108.encode_star(t, d, groups) with only the equations whose indices are in idx and whose row
    is in rows. Returns (cnf, names, counts)."""
    groups, idx, rows = set(groups), set(idx), set(rows)
    cnf = sa.CNF()
    A = [[[cnf.new() for c in range(t)] for r in range(t)] for i in range(d)]
    S = [[cnf.new() for r in range(t)] for i in range(d)]
    B = {(i, k): [cnf.new() for r in range(t)] for i, k in itertools.combinations(range(d), 2)}
    n = {g: 0 for g in STAR if g in groups}

    def bv(i, k):
        return None if i == k else B[(min(i, k), max(i, k))]

    def prods(M, vec, r):
        return [cnf.AND(M[r][c], vec[c]) for c in range(t)]

    for i in range(d):
        for j in range(d):
            g = m108.l_group(i, j)
            if g not in groups or i not in idx or j not in idx:
                continue
            b = bv(i, j)
            for r in range(t):
                if r not in rows:
                    continue
                lits = prods(A[j], S[i], r)
                if b is not None:
                    lits += [b[r]] + prods(A[i], b, r)
                cnf.xor_eq(lits, 0)
                n[g] += 1
    for i, k in itertools.combinations(range(d), 2):
        for j in range(d):
            if j in (i, k):
                continue
            g = m108.q_group(i, k, j)
            if g not in groups or not {i, k, j} <= idx:
                continue
            for r in range(t):
                if r not in rows:
                    continue
                cnf.xor_eq(prods(A[j], bv(i, k), r) + prods(A[i], bv(k, j), r)
                           + prods(A[k], bv(i, j), r), 0)
                n[g] += 1
    return cnf, (A, S, B, None, None), n


def build_sub(spec, case, groups, idx, rows):
    """(cnf, names, counts): the kept equations of (*), m42's normal form and the case's maps M, as
    m108.build_star."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    cnf, names, counts = encode_sub(t, d, groups, idx, rows)
    A, S, B = names[0], names[1], names[2]

    def unit(var, bit):
        cnf.clauses.append([var] if bit else [-var])

    for r in range(t):
        unit(S[0][r], (s0 >> r) & 1)
        for c in range(t):
            unit(A[0][r][c], (au >> (t * r + c)) & 1)
    for i in range(1, d):
        if phis[i] is None:
            continue
        for r in range(t):
            unit(B[(0, i)][r], (phis[i] >> r) & 1)
    counts["M"] = sum(m102.add_fixed_map(cnf, names, i, m102.a_of_t(au, tm))
                      for i, tm in zip((2, 3), case["maps"]))
    return cnf, names, counts


def failures(As, ss, B, t, d):
    """[(group, indices, rows)]: each equation of (*) that (A_i, s_i, b(i, k)) breaks, with the bit
    mask of the rows where it fails."""
    def bv(i, k):
        return 0 if i == k else B[(min(i, k), max(i, k))]

    out = []
    for g, ix in equations(d):
        if g[0] == "L":
            i, j = ix
            b = bv(i, j)
            diff = sa.mat_apply(As[j], ss[i], t) ^ b ^ sa.mat_apply(As[i], b, t)
        else:
            i, k, j = ix
            diff = (sa.mat_apply(As[j], bv(i, k), t) ^ sa.mat_apply(As[i], bv(k, j), t)
                    ^ sa.mat_apply(As[k], bv(i, j), t))
        if diff:
            out.append((g, ix, diff))
    return out


def holds(fails, groups, idx, rows):
    """Every kept equation holds."""
    idx, rmask = set(idx), sum(1 << r for r in set(rows))
    return not any(g in groups and set(ix) <= idx and m & rmask for g, ix, m in fails)


# ---------- the three passes ----------

def key_of(idx, rows, groups):
    """The kept equations, up to groups with none left (they give the same CNF)."""
    return (tuple(sorted(idx)), tuple(sorted(rows)),
            tuple(sorted(live_groups(groups, idx, rows))))


def reduce_item(solve):
    """solve(idx, rows, groups) -> status. Deletion passes over the indices, then the rows, then
    the live groups, each keeping the answer UNSAT. Returns a dict with the kept sets, why each
    was kept (SAT proves it is needed; UNKNOWN or SKIPPED does not) and the solve log, or kept None
    if everything together is not UNSAT."""
    cache, log = {}, []

    def oracle(idx, rows, groups):
        key = key_of(idx, rows, groups)
        if key not in cache:
            cache[key] = solve(list(key[0]), list(key[1]), list(key[2]))
            log.append([list(key[0]), list(key[1]), list(key[2]), cache[key]])
        return cache[key]

    out = {"kept_idx": None, "kept_rows": None, "kept_groups": None, "why": {}, "log": log}
    kept_idx, why_idx, _ = m108.minimize(lambda ix: oracle(ix, ALL_ROWS, STAR), IDX_DROP)
    if kept_idx is None:
        return out
    kept_rows, why_rows, _ = m108.minimize(lambda rs: oracle(kept_idx, rs, STAR), ROW_DROP)
    live = live_groups(STAR_DROP, kept_idx, kept_rows)
    kept_groups, why_groups, _ = m108.minimize(lambda gs: oracle(kept_idx, kept_rows, gs), live)
    out.update({"kept_idx": sorted(kept_idx), "kept_rows": sorted(kept_rows),
                "kept_groups": [g for g in STAR if g in kept_groups],
                "why": {"idx": {str(k): v for k, v in why_idx.items()},
                        "rows": {str(k): v for k, v in why_rows.items()}, "groups": why_groups},
                "solves": len(log)})
    out["equations"] = sum(count_sub(T, D, kept_groups, kept_idx, kept_rows).values())
    return out


def proven(entry):
    """Every kept index, row and group gave SAT when removed."""
    return entry["kept_idx"] is not None and all(
        v == "SAT" for part in entry["why"].values() for v in part.values())


# ---------- the solves ----------

def child(spec, case, groups, idx, rows, path):
    from pysat.solvers import Solver
    cnf, names, counts = build_sub(spec, case, groups, idx, rows)
    start = time.time()
    used = None
    for name in sa.SOLVERS:
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
           "clauses": len(cnf.clauses), "counts": counts, "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_sub(spec, case, groups, idx, rows, tag, part, cap, out_dir):
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--groups", json.dumps(list(groups)),
           "--idx", json.dumps(list(idx)), "--rows", json.dumps(list(rows)), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    if os.path.exists(path):
        os.remove(path)
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "tag": tag,
                "part": part, "idx": sorted(idx), "rows": sorted(rows),
                "groups": [g for g in STAR if g in groups], "kind": case["kind"],
                "maps": case["maps"], "type": m104.k_and_type(m103.space_of(case))[1],
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        B = {(i, k): v for i, k, v in res["B"]}
        fails = failures(res["A"], res["s"], B, T, D)
        chk = m100.check_model(spec, res)
        chk["t_maps"] = m102.extra_checks(spec, case, res)["t_maps"]
        row["check"] = {k: chk[k] for k in ("system", "normal_form", "anisotropic", "t_maps")}
        row["verified"] = chk["normal_form"] and chk["t_maps"] and holds(fails, groups, idx, rows)
        # the broken equations: which groups, indices and rows a refutation of this item needs
        row["broken_groups"] = sorted({g for g, _, _ in fails})
        row["broken_idx"] = sorted({i for _, ix, _ in fails for i in ix})
        row["broken_rows"] = sorted({r for _, _, m in fails for r in range(T) if (m >> r) & 1})
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def items_of(shard):
    items = m106.min_items()
    return [items[i] for i in SHARDS[shard]]


def run_reduce(shard, cap, minutes, out_dir):
    start = time.time()
    name = f"m109{shard}_rows.json"
    spec, case = m106.transfer_controls()[0]
    x = m102.inst_name(spec, case)
    append_row(out_dir, name,
               solve_sub(spec, case, STAR, ALL_IDX, ALL_ROWS, f"{x}_all", "control", cap, out_dir))
    mins = []
    for spec, case, part in items_of(shard):
        x = m102.inst_name(spec, case)
        step = [0]

        def solve(idx, rows, groups):
            if time.time() - start > minutes * 60:
                return "SKIPPED"
            step[0] += 1
            row = solve_sub(spec, case, groups, idx, rows, f"{x}_s{step[0]:02d}", part, cap,
                            out_dir)
            append_row(out_dir, name, row)
            return row["status"]

        entry = reduce_item(solve)
        entry.update({"instance": x, "part": part,
                      "type": m104.k_and_type(m103.space_of(case))[1]})
        mins.append(entry)
        save(out_dir, f"m109{shard}_min.json", mins)
        print(f"min {x}: {json.dumps({k: v for k, v in entry.items() if k != 'log'}, sort_keys=True)}",
              flush=True)
    short = {e["instance"][10:]: [e["kept_idx"], e["kept_rows"], e["kept_groups"]] for e in mins}
    print(f"SUMMARY run {shard} {json.dumps(short, sort_keys=True)}", flush=True)


# ---------- check and grade ----------

def run_check(shard, out_dir):
    g, info = {}, {}
    ref, _ = sa.encode(T, D, aniso=False, echelon=False)
    cnf, _, counts = encode_sub(T, D, STAR, ALL_IDX, ALL_ROWS)
    g["full_same_as_encode"] = ((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv)
                                == (m100.clause_hash(ref), len(ref.clauses), ref.nv))
    g["full_counts"] = counts == m108.STAR_COUNTS
    del ref, cnf
    g["sub_counts_by_hand"] = count_sub(T, D, STAR, SUB_IDX, SUB_ROWS) == SUB_COUNTS
    _, _, counts = encode_sub(T, D, STAR, SUB_IDX, SUB_ROWS)
    g["sub_counts_encoded"] = counts == SUB_COUNTS
    items = items_of(shard)
    spec, case, _ = items[0]
    ref, _, _ = m108.build_star(spec, case, STAR)
    cnf, _, counts = build_sub(spec, case, STAR, ALL_IDX, ALL_ROWS)
    g["build_same_as_m108"] = ((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv)
                               == (m100.clause_hash(ref), len(ref.clauses), ref.nv))
    g["m_counts"] = counts["M"] == 128
    info["clauses"] = len(cnf.clauses)
    del ref, cnf
    g["items"] = len(items) == len(SHARDS[shard])
    g["parts"] = all(p == ("core" if shard in "gh" else "k6") for _, _, p in items)
    info["items"] = [m102.inst_name(s, c) for s, c, _ in items]
    info["graded"] = g
    save(out_dir, f"m109{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({k: v for k, v in info.items() if k != 'graded'}, sort_keys=True)}",
          flush=True)


def grade(shard, out_dir):
    g, out = {}, {}
    st = m100.load(out_dir, f"m109{shard}_check.json")
    if st is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in st["graded"].items()})
    rows = m100.load(out_dir, f"m109{shard}_rows.json") or []
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g[f"verified_{r['tag']}"] = bool(r.get("verified"))
    ctrl = [r for r in rows if r["part"] == "control"]
    g["control_sat"] = len(ctrl) == 1 and ctrl[0]["status"] == "SAT" and bool(
        ctrl[0].get("verified"))
    mins = m100.load(out_dir, f"m109{shard}_min.json") or []
    g["min_ran"] = len(mins) == len(SHARDS[shard])
    # everything kept is m107's "M only" CNF, UNSAT for every one of these cases (m107e/f, m108g/h)
    g["all_unsat"] = bool(mins) and all(e["log"] and e["log"][0][3] == "UNSAT" for e in mins)
    out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                and r["check"].get("anisotropic"))
    out["min"] = {e["instance"][10:]: {"idx": e["kept_idx"], "rows": e["kept_rows"],
                                       "groups": e["kept_groups"], "equations": e.get("equations"),
                                       "proven": proven(e), "why": e["why"], "type": e["type"],
                                       "solves": e.get("solves")} for e in mins}
    out["statuses"] = {}
    for r in rows:
        out["statuses"][r["status"]] = out["statuses"].get(r["status"], 0) + 1
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "reduce", "grade", "child"], default="check")
    ap.add_argument("--shard", choices=sorted(SHARDS), default="g")
    ap.add_argument("--cap-seconds", type=float, default=120.0)
    ap.add_argument("--minutes", type=float, default=200.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--groups")
    ap.add_argument("--idx")
    ap.add_argument("--rows")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), json.loads(args.groups),
              json.loads(args.idx), json.loads(args.rows), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "reduce":
        run_reduce(args.shard, args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m109{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k != "graded"}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
