# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m100: the rank-0 sweep of Lemma 103 for every class of A_u in (B7)_8 (t = 8, dim V = 11,
dim P = 7), with m42's encoding and hints unchanged (cube_groups/m100-predictions.md, notes/a92.md).

What came back on 2026-10-24 (job m99, notes/a92.md): every graded check held (24 of 24). (B7)_8 has
13 pair orbits and 68 classes of A_u, (B6)_8 51 and 422, as Lemma 101 counts by hand, and the six
pilot instances (whole classes, no split) were all UNKNOWN at 240 s.

Lemma 103 (by hand, notes/a92.md; Lemma 93 of a52.md at t = 8): if every A_n with n in N = ker phi
vanishes on X_1 = ker A_u, then beta(n, n') = 0 for all n, n' in N. For one class of A_u, the case
"every A_n (n in N) vanishes on X_1" is one instance: m42's instance plus A_(v_i) X_1 = 0 and
beta(v_i, v_j) = 0 for 1 <= i < j < 4. It is a case split on the system and needs no symmetry
argument. If it is UNSAT, every system of the class has an element of N of rank >= 1 on X_1, and
by Lemma 103 (a) a later second-matrix split needs only its representatives of rank >= 1.

Parts (one shard of the 13 pairs per job):

    check    the 68 representatives of m99 (kernel, image, rank, sizes, d); this module's
             encode_fixed equals m42's on a real instance; the relax CNF has none of the 2047
             anisotropy clauses; the sweep adds 144 conditions
    control  two classes of the shard with anisotropy switched off (a positive control: a model
             must pass the sweep conditions and (*), checked outside the encoder)
    sweep    every class of the shard, capped
    grade    the graded checks of m100-predictions.md

Usage: python m100.py --part check|control|sweep|grade --shard a|b [--cap-seconds S] [--out-dir D]
"""
import argparse
import hashlib
import itertools
import json
import os
import subprocess
import sys
import time

import m42
import sat_aniso as sa

T, D, P = 8, 11, 7
KD = D - P                      # u, v_1, v_2, v_3 span N = ker phi
SWEEP_CONDITIONS = (KD - 1) * (T - 3) * T + (KD - 1) * (KD - 2) // 2 * T     # 120 + 24
# job m99 (compete-results/m99-b78-classes-v1/out/m99_classes_t8_B7.json): per pair orbit,
# ker A_u, Im A_u (echelon bases) and the classes [representative A_u, class size]
PAIRS = [
    ((16, 8, 4, 2, 1), (4, 2, 1), [(2113664, 168)]),
    ((16, 8, 4, 2, 1), (8, 4, 2), [(541097984, 168)]),
    ((16, 8, 4, 2, 1), (8, 4, 3), [(541098112, 168)]),
    ((16, 8, 4, 2, 1), (32, 2, 1), [(35184372105344, 48), (35184372105376, 48),
                                    (70368744185984, 24), (70368744186016, 24),
                                    (70368744210464, 24)]),
    ((16, 8, 4, 2, 1), (32, 4, 2), [(35184376315904, 96), (70368746307584, 72)]),
    ((16, 8, 4, 2, 1), (32, 4, 3), [(35184376316032, 48), (35184376324256, 48),
                                    (70368746307712, 24), (70368746315936, 48)]),
    ((16, 8, 4, 2, 1), (33, 4, 2), [(35184376315936, 96), (70368746307648, 72)]),
    ((16, 8, 4, 2, 1), (64, 32, 1), [(9077567998918784, 12), (9077567998918816, 24),
                                     (9077567998918880, 12), (9112752371007616, 8),
                                     (9112752371007648, 24), (9147936743096384, 24),
                                     (9183121115185216, 24), (9183121115185248, 24),
                                     (18049582881570944, 4), (18049582881570976, 12)]),
    ((16, 8, 4, 2, 1), (64, 32, 2), [(9077567998951424, 48), (9112752371040256, 32),
                                     (9147936743112704, 24), (9183121115201536, 48),
                                     (18049582881603584, 16)]),
    ((16, 8, 4, 2, 1), (64, 32, 3), [(9077567998951552, 12), (9077567998959776, 24),
                                     (9077567998976224, 12), (9112752371040384, 8),
                                     (9112752371048608, 24), (9147936743112768, 24),
                                     (9183121115201600, 24), (9183121115209824, 24),
                                     (18049582881603712, 4), (18049582881611936, 12)]),
    ((16, 8, 4, 2, 1), (64, 33, 2), [(9077567998951488, 32), (9112752371040352, 32),
                                     (9147936743112832, 8), (9183121115201696, 16),
                                     (18049582881603616, 16), (18155135997845632, 16),
                                     (18225504742023360, 16), (27056782136344608, 16),
                                     (27267888368853216, 16)]),
    ((16, 8, 4, 2, 1), (128, 64, 32), [(2323998145211531264, 21), (2324033329583620096, 56),
                                       (2324068513955708928, 42), (2333075713210449920, 24),
                                       (2333110897582538752, 24), (9241421619736346624, 1)]),
    ((16, 8, 4, 2, 1), (128, 64, 33), [(2323998145211531392, 12), (2324033329583620256, 24),
                                       (2324068513955709120, 24), (2324103698327797984, 24),
                                       (2333005344466272384, 12), (2333075713210450112, 24),
                                       (2333110897582538976, 24), (4647749999818440736, 6),
                                       (4656757199073181728, 6), (4665764398327922720, 8),
                                       (9241421619736346656, 1), (9250428818991087648, 3)]),
]
# m99's invariants: d = dim(X_1 n R) per pair orbit, and the number of classes per pair orbit
M99_D = (3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 0, 0)
M99_CLASSES = (1, 1, 1, 5, 2, 4, 2, 10, 5, 10, 9, 6, 12)
SHARDS = {"a": tuple(range(0, 9)), "b": tuple(range(9, 13))}
CONTROLS = {"a": ((0, 0), (3, 0)), "b": ((9, 0), (11, 0))}


# ---------- linear algebra on F_2^8 ----------

def span(vecs):
    out = {0}
    for v in vecs:
        out |= {v ^ w for w in out}
    return out


def kernel_basis(A, t=T):
    """An echelon basis of ker A (A as in sat_aniso: bit t * r + c is the entry (r, c))."""
    basis = []
    for x in range(1, 1 << t):
        if sa.mat_apply(A, x, t) == 0 and sa.rank_f2(basis + [x]) > len(basis):
            basis.append(x)
    return basis


def image(A, t=T):
    return {sa.mat_apply(A, x, t) for x in range(1 << t)}


def meet_dim(a, b):
    return len(span(a) & span(b)).bit_length() - 1


# ---------- the instances ----------

def spec_of(pi, ci):
    x1, r, cls = PAIRS[pi]
    rep, size = cls[ci]
    return {"name": m42.instance_name(T, P, pi, ci), "kind": "main", "t": T, "d": D, "p": P,
            "pair": pi, "cls": ci, "x1": list(x1), "r": list(r), "au": rep, "class_size": size,
            "dmeet": meet_dim(x1, r)}


def shard_specs(shard):
    return [spec_of(pi, ci) for pi in SHARDS[shard] for ci in range(len(PAIRS[pi][2]))]


def encode_fixed(t, d, au, s0, phis, aniso=True):
    """m42.encode_fixed, with the anisotropy clauses of sat_aniso.encode switched on or off."""
    cnf, names = sa.encode(t, d, aniso=aniso, echelon=False)
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
    return cnf, names


def add_sweep(cnf, names, t, kd, au):
    """Lemma 103: A_(v_i) y = 0 for y in a basis of ker A_u and beta(v_i, v_j) = 0, for
    0 < i < j < kd. Returns the number of conditions added."""
    A, B = names[0], names[2]
    n = 0
    for i in range(1, kd):
        for y in kernel_basis(au, t):
            for row in range(t):
                cnf.xor_eq([A[i][row][c] for c in range(t) if (y >> c) & 1], 0)
                n += 1
    for i, j in itertools.combinations(range(1, kd), 2):
        for row in range(t):
            cnf.clauses.append([-B[(i, j)][row]])
            n += 1
    return n


def build(spec, relax=False):
    """(cnf, names, hints, sweep) of the sweep instance; relax drops the anisotropy clauses."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    cnf, names = encode_fixed(t, d, au, s0, phis, aniso=not relax)
    hints = m42.add_hints(cnf, names, t, kd, au, s0, pvecs)
    return cnf, names, hints, add_sweep(cnf, names, t, kd, au)


def aniso_clauses(cnf, t):
    """The all-positive clauses of length t over parity definitions (m95.relax's test)."""
    return sum(1 for c in cnf.clauses
               if len(c) == t and all(x > 0 and cnf.defs.get(x, ("",))[0] == "xor" for x in c))


def clause_hash(cnf):
    h = hashlib.sha256()
    for c in cnf.clauses:
        h.update((" ".join(map(str, c)) + "\n").encode())
    return h.hexdigest()


# ---------- solving ----------

def child(spec, relax, path):
    from pysat.solvers import Solver
    cnf, names, _, _ = build(spec, relax)
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
           "clauses": len(cnf.clauses), "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def check_model(spec, res):
    """A SAT answer read back outside the encoder: (*), the normal form, the sweep conditions and
    anisotropy, each separately."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    As, ss = res["A"], res["s"]
    B = {(i, k): v for i, k, v in res["B"]}
    at, sv = sa.tables(As, ss, B, d)
    ker = kernel_basis(au, t)
    return {"system": sa.is_system(at, sv, d, t),
            "normal_form": (As[0] == au and ss[0] == s0
                            and all(phis[i] is None or B[(0, i)] == phis[i] for i in range(1, d))),
            "sweep": (all(sa.mat_apply(As[i], y, t) == 0 for i in range(1, kd) for y in ker)
                      and all(B[(i, j)] == 0 for i, j in itertools.combinations(range(1, kd), 2))),
            "anisotropic": sa.anisotropic(sv)}


def solve_one(spec, relax, budget, out_dir):
    tag = spec["name"] + ("_relax" if relax else "_sweep")
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--relax", str(int(relax)), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=budget, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({k: spec[k] for k in ("name", "pair", "cls", "dmeet", "class_size")})
    row.update({"relax": relax, "wall_seconds": round(time.time() - start, 2),
                "budget_seconds": budget})
    if res["status"] == "SAT":
        row["check"] = check_model(spec, res)
        need = ("system", "normal_form", "sweep") + (() if relax else ("anisotropic",))
        row["verified"] = all(row["check"][k] for k in need)
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


# ---------- the parts ----------

def run_check(shard, out_dir):
    g = {}
    reps = [(pi, ci) for pi in range(len(PAIRS)) for ci in range(len(PAIRS[pi][2]))]
    g["classes_68"] = len(reps) == 68
    g["classes_per_pair"] = tuple(len(p[2]) for p in PAIRS) == M99_CLASSES
    g["sizes_168"] = all(sum(s for _, s in p[2]) == 168 for p in PAIRS)
    g["d_as_m99"] = tuple(meet_dim(x1, r) for x1, r, _ in PAIRS) == M99_D
    ok = True
    for x1, r, cls in PAIRS:
        for rep, _ in cls:
            ok = ok and (sa.rank_f2(sa.rows_of(rep, T)) == 3 and span(kernel_basis(rep)) == span(x1)
                         and image(rep) == span(r))
    g["reps_kernel_image"] = ok
    g["shards_cover"] = sorted(SHARDS["a"] + SHARDS["b"]) == list(range(len(PAIRS)))
    spec = spec_of(*CONTROLS[shard][0])
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    theirs, _ = m42.encode_fixed(t, d, au, s0, phis)
    h_theirs, n_theirs = clause_hash(theirs), len(theirs.clauses)
    del theirs
    ours, _ = encode_fixed(t, d, au, s0, phis)
    g["encode_as_m42"] = (clause_hash(ours), len(ours.clauses)) == (h_theirs, n_theirs)
    g["aniso_2047"] = aniso_clauses(ours, t) == (1 << d) - 1
    del ours
    cnf, _, hints, sweep = build(spec, relax=True)
    g["relax_no_aniso"] = aniso_clauses(cnf, t) == 0
    g["sweep_144"] = sweep == SWEEP_CONDITIONS == 144
    info = {"graded": g, "hints": hints, "sweep": sweep, "relax_clauses": len(cnf.clauses),
            "full_clauses": n_theirs, "spec": spec["name"]}
    with open(os.path.join(out_dir, f"m100{shard}_check.json"), "w") as f:
        json.dump(info, f, indent=1)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} hints {hints} "
          f"sweep {sweep} relax_clauses {len(cnf.clauses)} full_clauses {n_theirs}", flush=True)


def append_row(out_dir, shard, row):
    path = os.path.join(out_dir, f"m100{shard}_rows.json")
    rows = load(out_dir, f"m100{shard}_rows.json") or []
    rows.append(row)
    with open(path, "w") as f:
        json.dump(rows, f, indent=1)


def run_control(shard, cap, out_dir):
    counts = {}
    for pi, ci in CONTROLS[shard]:
        row = solve_one(spec_of(pi, ci), True, cap, out_dir)
        append_row(out_dir, shard, row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1
    print(f"SUMMARY control {shard} {json.dumps(counts, sort_keys=True)} cap {cap}", flush=True)


def run_sweep(shard, cap, out_dir):
    counts, by_d = {}, {}
    for spec in shard_specs(shard):
        row = solve_one(spec, False, cap, out_dir)
        append_row(out_dir, shard, row)
        counts[row["status"]] = counts.get(row["status"], 0) + 1
        key = f"d{spec['dmeet']}"
        by_d.setdefault(key, {})
        by_d[key][row["status"]] = by_d[key].get(row["status"], 0) + 1
    print(f"SUMMARY sweep {shard} {json.dumps(counts, sort_keys=True)} by_d "
          f"{json.dumps(by_d, sort_keys=True)} cap {cap}", flush=True)


def load(out_dir, name):
    try:
        with open(os.path.join(out_dir, name)) as f:
            return json.load(f)
    except (OSError, ValueError):
        return None


def grade(shard, out_dir):
    g = {}
    chk = load(out_dir, f"m100{shard}_check.json")
    if chk is None:
        g["check_ran"] = False
    else:
        g.update({"check_" + k: v for k, v in chk["graded"].items()})
    rows = load(out_dir, f"m100{shard}_rows.json") or []
    sweep = [r for r in rows if not r["relax"]]
    control = [r for r in rows if r["relax"]]
    g["sweep_complete"] = sorted(r["name"] for r in sweep) == sorted(
        s["name"] for s in shard_specs(shard))
    g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
    for r in rows:
        if r["status"] == "SAT":
            g["verified_" + r["name"] + ("_relax" if r["relax"] else "_sweep")] = bool(
                r.get("verified"))
    out = {"graded": g,
           "sweep": {r["name"]: [r["status"], r["wall_seconds"], r["dmeet"]] for r in sweep},
           "control": {r["name"]: [r["status"], r["wall_seconds"]] for r in control},
           "unsat": sorted(r["name"] for r in sweep if r["status"] == "UNSAT")}
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "control", "sweep", "grade", "child"],
                    default="check")
    ap.add_argument("--shard", choices=sorted(SHARDS), default="a")
    ap.add_argument("--cap-seconds", type=float, default=180.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--relax", type=int, default=0)
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), bool(args.relax), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.out_dir)
    elif args.part == "control":
        run_control(args.shard, args.cap_seconds, args.out_dir)
    elif args.part == "sweep":
        run_sweep(args.shard, args.cap_seconds, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        with open(os.path.join(args.out_dir, f"m100{args.shard}_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        st = {}
        for s, _, _ in out["sweep"].values():
            st[s] = st.get(s, 0) + 1
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} "
              f"failed {bad[:12]} sweep {json.dumps(st, sort_keys=True)} control "
              f"{json.dumps(out['control'], sort_keys=True)} unsat {out['unsat']}", flush=True)


if __name__ == "__main__":
    main()
