# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m95: every (type, orbit) of an element of rank 4 at t = 8 and dim V = 11 (Lemmas 95 and 96,
notes/a85.md, a86.md, a87.md; cube_groups/m95-predictions.md).

What came back on 2026-10-23: job m94's pilot, type (N4) with W in m93's orbit of 10080 spaces,
was UNSAT in 2.57 s (142832 variables, 905882 clauses), all 9 graded checks held. By its rule
("UNSAT within 10 minutes"), the other orbits of (N4) follow, and then the types with d = 3.

Setting as in m94.py: case_b_shapes.encode_shape(8, 4, 'c'), the tuple M_(v_1), M_(v_2), M_(v_3)
fixed to the basis m93 recorded for the orbit (Lemma 96), (S) and (a) of Lemma 38 as in m94, and
T = A_u on [e_4], ..., [e_7] free. D = T^(-1)(X_1 n R) has dimension d in {3, 4} (Lemma 95):

    d = 4 (type (N4)): m94.encode_n4, unchanged: rows 4 to 7 of every A_u e_c (c >= 4) are 0, and
          no non-empty set of these columns adds up to 0 in rows 0 to 3.
    d = 3 (types (N3) and (F3) together): D = ker f is a hyperplane of F_2^4 invariant under W
          (Lemma 95(d)), one instance for each invariant hyperplane of the recorded basis. With
          l0 the lowest set bit of f and e_l the vector [e_(4+l)], D has the basis
          e_l + f_l e_l0 (l != l0), and e_l0 is outside D. So
            (D)   rows 4 to 7 of A_u applied to each basis vector of D are 0 (12 equations),
            (O)   rows 4 to 7 of A_u e_(4+l0) are not all 0 (one clause), and
            (inv) no non-empty set of the columns A_u e_4, ..., A_u e_7 adds up to 0 (15 clauses,
                  over all 8 rows, as the columns need not lie in X_1).
          The (D) and (O) conditions say exactly that T(D) lies in X_1 and T(F_2^4) does not, so
          that D = T^(-1)(X_1 n R) for any system whose D is ker f.

So the rank-4 case at (8, 11) is closed if every instance of both groups is UNSAT: 23 of type
(N4) and one per (orbit, invariant hyperplane) for d = 3. Each UNSAT rests on Lemmas 38, 39, 94,
95 and 96 (hand arguments no human has checked), on m93's orbit list, and on the encoding.

Group a (job m95a): the 23 orbits of (N4), each solved by python-sat and then certified: a
  standalone CaDiCaL writes a DRAT proof and drat-trim checks it (cert1.py's tools, unchanged).
  Then a ladder on the pilot's CNF: without the 2^11 - 1 anisotropy clauses ("relax"; a model
  must be a system in the normal form with every new condition, and not anisotropic), the same
  at (6, 3), and with one family of the new clauses dropped at a time.
Group b (job m95b): every (orbit, hyperplane) with d = 3, solved by python-sat.

Parts: selfcheck (m93's orbits recomputed with m93.py, the hyperplanes, the encodings against
m94's), controls (cert1's three tool controls, group a), solve, ladder (group a), grade.

Usage: python m95.py --part selfcheck|controls|solve|ladder|grade --group a|b [--tools tools]
       [--cap-seconds S] [--minutes M] [--out-dir DIR]
"""
import argparse
import json
import os
import statistics
import subprocess
import sys
import tempfile
import time

import case_b_shapes as csh
import m94
import sat_aniso as sa

T, K = 8, 4
GROUPS = ("a", "b")
ORBITS_FILE = "m95_orbits.json"
PILOT = (1, 64, 1056)
# m93's run (compete-results/m93-commuting-orbits-v1, 2026-10-23): orbits and subspaces.
M93 = {"all": (79, 160408), "n4": (23, 47595), "hyper": (73, 153240)}
# m94's run: [vars, clauses, start, first_var] of the pilot and of the (6, 3) control.
M94_SIZES = {(8, 4): [142832, 905882, 905367, 142785], (6, 3): [23124, 136183, 136023, 23113]}
FAMILIES = ("units", "inv", "lin", "a")
LADDER = (("relax_t6", "t6", ()), ("relax", "t8", ()), ("drop_units", None, ("units",)),
          ("drop_inv", None, ("inv",)), ("drop_lin", None, ("lin",)), ("drop_a", None, ("a",)),
          ("drop_lin_a", None, ("lin", "a")))


# ---------- hyperplanes of F_2^n (vectors: bit l is the coordinate of [e_(k+l)]) ----------

def parity(x):
    return bin(x).count("1") & 1


def row_times(f, M):
    """The row vector f M (bit r of f is coordinate r)."""
    n = len(M)
    return sum((sum(M[r][c] for r in range(n) if f >> r & 1) & 1) << c for c in range(n))


def apply(M, v):
    """M v for a column vector v."""
    n = len(M)
    return sum((sum(M[r][c] for c in range(n) if v >> c & 1) & 1) << r for r in range(n))


def hyperplanes(Ms):
    """The f != 0 with f M in {0, f} for every M: then ker f is invariant (as in m93.flags)."""
    n = len(Ms[0])
    return [f for f in range(1, 1 << n) if all(row_times(f, M) in (0, f) for M in Ms)]


def low_bit(f):
    return (f & -f).bit_length() - 1


def d_basis(f, n):
    """A basis of D = ker f: e_l + f_l e_l0 for l != l0."""
    l0 = low_bit(f)
    return [(1 << l) | ((f >> l & 1) << l0) for l in range(n) if l != l0]


def invariant(Ms, f):
    """ker f mapped into itself by every M, checked vector by vector."""
    n = len(Ms[0])
    D = [v for v in range(1 << n) if not parity(f & v)]
    return len(D) == 1 << (n - 1) and all(not parity(f & apply(M, v)) for M in Ms for v in D)


# ---------- the encoding ----------

def encode_rank4(t, k, Ms, f=None, drop=()):
    """(cnf, names, info): encode_shape(t, k, 'c') with M_(v_i) = Ms[i - 1], (S) and (a), and
    d = 4 (f None: m94.encode_n4's clauses in its order) or d = 3 with D = ker f. The families in
    drop are left out."""
    n = t - k
    if n != k or len(Ms) != k - 1 or not m94.check_tuple(Ms):
        raise ValueError("needs t = 2 k and k - 1 commuting matrices spanning a space of "
                         "dimension k - 1 without I")
    if f is not None and not invariant(Ms, f):
        raise ValueError("ker f is not invariant under the matrices")
    cnf, names = csh.encode_shape(t, k, "c")
    A, B = names[0], names[2]
    info = {"start": len(cnf.clauses), "first_var": cnf.nv + 1, "d": 4 if f is None else 3,
            "drop": list(drop)}
    units = outside = 0
    if "units" not in drop:
        if f is None:
            for r in range(k, t):
                for c in range(k, t):
                    cnf.clauses.append([-A[0][r][c]])
                    units += 1
        else:
            for v in d_basis(f, n):
                for r in range(k, t):
                    cnf.xor_eq([A[0][r][k + l] for l in range(n) if v >> l & 1], 0)
                    units += 1
            l0 = low_bit(f)
            cnf.clauses.append([A[0][r][k + l0] for r in range(k, t)])
            outside += 1
    inv = 0
    if "inv" not in drop:
        rows = range(k) if f is None else range(t)
        for sel in range(1, 1 << n):
            cs = [k + c for c in range(n) if (sel >> c) & 1]
            if len(cs) == 1:
                cnf.clauses.append([A[0][r][cs[0]] for r in rows])
            else:
                cnf.clauses.append([cnf.xor_def([A[0][r][c] for c in cs]) for r in rows])
            inv += 1
    lin = 0
    if "lin" not in drop:
        for i in range(1, k):
            M = Ms[i - 1]
            for j in range(n):
                for r in range(t):
                    cnf.xor_eq([A[i][r][k + j]] + [A[0][r][k + l] for l in range(n) if M[l][j]],
                               0)
                    lin += 1
    a_units = 0
    if "a" not in drop:
        for i in range(1, k):
            M = Ms[i - 1]
            for j in range(1, t):
                for l in range(n):
                    v = B[(i, k - 1 + j)][k + l]
                    cnf.clauses.append([v] if j >= k and M[l][j - k] else [-v])
                    a_units += 1
    info.update({"units": units, "outside": outside, "inv": inv, "lin": lin, "a_units": a_units,
                 "vars": cnf.nv, "clauses": len(cnf.clauses)})
    return cnf, names, info


def relax(cnf, t):
    """Drops the anisotropy clauses of sat_aniso.encode: the all-positive clauses of length t
    whose variables are all parity definitions (no other clause of these CNFs has that form).
    Returns how many were dropped."""
    keep, dropped = [], 0
    for c in cnf.clauses:
        if (len(c) == t and all(x > 0 and cnf.defs.get(x, ("",))[0] == "xor" for x in c)):
            dropped += 1
        else:
            keep.append(c)
    cnf.clauses = keep
    return dropped


def col(A, c, t):
    return sa.mat_apply(A, 1 << c, t)


def fixed_parts(As, B, t, k, Ms, f=None):
    """Each family of new conditions read back from a decoded model."""
    n = t - k
    low = (1 << k) - 1
    tc = [col(As[0], k + c, t) for c in range(n)]

    def at(v):
        x = 0
        for l in range(n):
            if v >> l & 1:
                x ^= tc[l]
        return x

    if f is None:
        units = all(not x & ~low for x in tc)
    else:
        units = (all(not at(v) & ~low for v in d_basis(f, n))
                 and bool(tc[low_bit(f)] & ~low))
    lin = a = True
    for i in range(1, k):
        M = Ms[i - 1]
        for j in range(n):
            want = 0
            for l in range(n):
                if M[l][j]:
                    want ^= tc[l]
            lin = lin and col(As[i], k + j, t) == want
        for j in range(1, t):
            want = sum(M[l][j - k] << (k + l) for l in range(n)) if j >= k else 0
            a = a and (B[(i, k - 1 + j)] >> k) == want >> k
    return {"units": units, "inv": sa.rank_f2(tc) == n, "lin": lin, "a": a}


# ---------- the orbits (m93.py, downloaded unchanged) ----------

def orbit_list():
    import m93
    tb = m93.Tables()
    checks, _ = tb.checks()
    d3 = m93.run(tb, 3)
    out = []
    for i, o in enumerate(d3["orbits"]):
        fl = m93.flags(tb, o["basis"])
        Ms = [m94.m_of(x, 4) for x in o["basis"]]
        out.append({"index": i, "basis": o["basis"], "size": o["size"], "n4": fl["n4"],
                    "f3": fl["f3"], "singular": fl["singular"], "m93_hyperplanes": fl["hyperplanes"],
                    "hyper": hyperplanes(Ms)})
    return out, all(checks.values()), d3, m93.reps_ok(d3["orbits"])


def group_specs(group, orbits):
    if group == "a":
        return [{"name": f"n4_o{o['index']:02d}_s{o['size']}", "kind": "n4", "t": T, "k": K,
                 "w": o["basis"], "f": None, "orbit": o["index"], "size": o["size"]}
                for o in orbits if o["n4"]]
    return [{"name": f"d3_o{o['index']:02d}_f{f:02d}", "kind": "d3", "t": T, "k": K,
             "w": o["basis"], "f": f, "orbit": o["index"], "size": o["size"]}
            for o in orbits for f in o["hyper"]]


def selfcheck(out_dir):
    start = time.time()
    orbits, tables_ok, d3, reps_ok = orbit_list()
    g = {}
    g["m93_tables"] = tables_ok
    g["m93_dim3"] = (d3["complete"] and d3["double_count_ok"]
                     and d3["subspaces"] == d3["orbit_size_sum"] and reps_ok)

    def count(pred):
        sel = [o for o in orbits if pred(o)]
        return len(sel), sum(o["size"] for o in sel)

    g["orbits_all"] = count(lambda o: True) == M93["all"]
    g["orbits_n4"] = count(lambda o: o["n4"]) == M93["n4"]
    g["orbits_hyper"] = count(lambda o: o["hyper"]) == M93["hyper"]
    g["hyper_counts"] = all(len(o["hyper"]) == o["m93_hyperplanes"] for o in orbits)
    g["hyper_invariant"] = all(invariant([m94.m_of(x, 4) for x in o["basis"]], f)
                               for o in orbits for f in o["hyper"])
    g["pilot_in_n4"] = any(tuple(o["basis"]) == PILOT and o["size"] == 10080 and o["n4"]
                           for o in orbits)
    sizes = {}
    for (t, k), Ms in (((8, 4), m94.pilot_ms()), ((6, 3), [m94.SHIFT, m94.SHIFT2])):
        mine, _, info = encode_rank4(t, k, Ms)
        theirs, _, _ = m94.encode_n4(t, k, Ms)
        sizes[f"{t},{k}"] = [info["vars"], info["clauses"], info["start"], info["first_var"]]
        g[f"encode_t{t}"] = (mine.clauses == theirs.clauses and mine.nv == theirs.nv
                             and sizes[f"{t},{k}"] == M94_SIZES[(t, k)])
        n_aniso = relax(mine, t)
        g[f"aniso_t{t}"] = n_aniso == (1 << (t + k - 1)) - 1
        del mine, theirs
    specs = {gr: group_specs(gr, orbits) for gr in GROUPS}
    out = {"graded": g, "orbits": orbits, "sizes": sizes,
           "instances": {gr: len(s) for gr, s in specs.items()},
           "seconds": round(time.time() - start, 1)}
    with open(os.path.join(out_dir, ORBITS_FILE), "w") as f:
        json.dump(out, f, indent=1)
    return out


# ---------- solving ----------

def ms_of(spec):
    if spec.get("t") == 6:
        return [m94.SHIFT, m94.SHIFT2]
    return [m94.m_of(x, 4) for x in spec["w"]]


def build(spec):
    cnf, names, info = encode_rank4(spec["t"], spec["k"], ms_of(spec), spec.get("f"),
                                    tuple(spec.get("drop", ())))
    if spec.get("relax"):
        if spec.get("f") is not None:
            raise ValueError("relax is for d = 4 only (the one-to-one clauses of d = 3 have "
                             "length t)")
        info["aniso_dropped"] = relax(cnf, spec["t"])
        info["clauses"] = len(cnf.clauses)
    return cnf, names, info


def child(spec, path):
    from pysat.solvers import Solver
    cnf, names, info = build(spec)
    if spec.get("dimacs"):
        import cert1 as c1
        info["dimacs_vars"] = c1.write_dimacs(cnf.clauses, cnf.nv, spec["dimacs"])
    with open(path + ".size", "w") as f:
        json.dump(info, f)
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
    res = {"status": "SAT" if ok else "UNSAT", "solver": used,
           "seconds": round(time.time() - start, 2)}
    if ok:
        d = spec["t"] + spec["k"] - 1
        As, ss, B = sa.decode(s.get_model(), names, spec["t"], d)
        res.update({"A": As, "s": ss, "B": [[i, j, v] for (i, j), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def verify(res, spec):
    """A model read back by brute force: the system (*) on all pairs, anisotropy, the normal form
    of shape (c), and each family of new conditions that the CNF kept."""
    t, k = spec["t"], spec["k"]
    d = t + k - 1
    As, ss = res["A"], res["s"]
    B = {(i, j): v for i, j, v in res["B"]}
    at, sv = sa.tables(As, ss, B, d)
    parts = fixed_parts(As, B, t, k, ms_of(spec), spec.get("f"))
    kept = [x for x in FAMILIES if x not in spec.get("drop", ())]
    return {"system": sa.is_system(at, sv, d, t), "anisotropic": sa.anisotropic(sv),
            "shape": csh.in_shape(As, ss, B, t, k, "c"), "parts": parts,
            "kept_hold": all(parts[x] for x in kept)}


def solve_one(spec, cap, out_dir, tmp=None):
    path = os.path.join(out_dir, spec["name"] + ".child.json")
    sp = dict(spec)
    if tmp:
        sp["dimacs"] = os.path.join(tmp, "i.cnf")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(sp),
           "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    try:
        with open(path + ".size") as f:
            res["cnf"] = json.load(f)
    except (OSError, ValueError):
        res["cnf"] = None
    for p in (path, path + ".size"):
        if os.path.exists(p):
            os.remove(p)
    res.update(spec)
    res.update({"wall_seconds": round(time.time() - start, 2), "cap_seconds": cap})
    if res["status"] == "SAT":
        res["check"] = verify(res, spec)
        with open(os.path.join(out_dir, spec["name"] + ".model.json"), "w") as f:
            json.dump(res, f)
    return res


def certify(tools, res, tmp):
    """cert1's certify step on the DIMACS file the child wrote: CaDiCaL with a DRAT proof, then
    drat-trim."""
    import cert1 as c1
    cnf, prf = os.path.join(tmp, "i.cnf"), os.path.join(tmp, "i.drat")
    out = {"cnf_sha256": c1.sha256(cnf)}
    cad, _ = c1.run_cadical(tools, cnf, prf)
    out["cadical"] = cad
    out["proof_bytes"] = os.path.getsize(prf) if os.path.exists(prf) else 0
    out["drat"] = c1.run_drat(tools, cnf, prf) if cad["status"] == "UNSAT" else None
    out["cert"] = ("VERIFIED" if out["drat"] and out["drat"]["verified"]
                   else cad["status"] if cad["status"] != "UNSAT" else "NOT_VERIFIED")
    for p in (cnf, prf):
        if os.path.exists(p):
            os.remove(p)
    res.update(out)


def line(res):
    cnf = res.get("cnf") or {}
    extra = ""
    if "cert" in res:
        extra = (f" cert {res['cert']} cadical {res['cadical'].get('seconds')} s drat "
                 f"{(res.get('drat') or {}).get('seconds')} s proof {res.get('proof_bytes')} B")
    if "check" in res:
        extra += f" check {json.dumps(res['check'], sort_keys=True)}"
    return (f"solve {res['name']}: {res['status']} seconds {res.get('seconds')} wall "
            f"{res['wall_seconds']} vars {cnf.get('vars')} clauses {cnf.get('clauses')}{extra}")


def run_solve(group, tools, cap, minutes, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, ORBITS_FILE)) as f:
        st = json.load(f)
    if not all(st["graded"].values()):
        raise SystemExit("selfcheck failed: nothing solved")
    specs = group_specs(group, st["orbits"])
    rows, counts = [], {}
    for sp in specs:
        if time.time() - start > minutes * 60:
            res = dict(sp, status="SKIPPED", wall_seconds=0)
        elif group == "a":
            with tempfile.TemporaryDirectory() as tmp:
                res = solve_one(sp, cap, out_dir, tmp)
                if res["status"] == "UNSAT":
                    certify(tools, res, tmp)
        else:
            res = solve_one(sp, cap, out_dir)
        res.pop("A", None), res.pop("s", None)
        rows.append(res)
        key = res["status"] + ("_" + res["cert"] if "cert" in res else "")
        counts[key] = counts.get(key, 0) + 1
        print(line(res), flush=True)
    with open(os.path.join(out_dir, f"m95{group}_rows.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print(f"SUMMARY solve group {group} instances {len(specs)} {json.dumps(counts, sort_keys=True)} "
          f"seconds {round(time.time() - start)}", flush=True)


def ladder_specs():
    base = {"t": T, "k": K, "w": list(PILOT), "f": None}
    out = []
    for name, kind, drop in LADDER:
        if kind == "t6":
            out.append({"name": name, "t": 6, "k": 3, "w": None, "f": None, "relax": True})
        else:
            out.append(dict(base, name=name, relax=kind == "t8", drop=list(drop)))
    return out


def run_ladder(caps, minutes, out_dir):
    start = time.time()
    rows = []
    for sp in ladder_specs():
        cap = caps[0] if sp.get("relax") else caps[1]
        if time.time() - start > minutes * 60:
            res = dict(sp, status="SKIPPED", wall_seconds=0)
        else:
            res = solve_one(sp, cap, out_dir)
        res.pop("A", None), res.pop("s", None), res.pop("B", None)
        rows.append(res)
        print(line(res), flush=True)
    with open(os.path.join(out_dir, "m95a_ladder.json"), "w") as f:
        json.dump(rows, f, indent=1)
    print(f"SUMMARY ladder " + " ".join(f"{r['name']} {r['status']}" for r in rows), flush=True)


def run_controls(tools, out_dir):
    """cert1's three tool controls: PHP(6, 5) UNSAT with a VERIFIED proof, an empty proof
    rejected, PHP(5, 5) SAT with a model that satisfies every clause."""
    import cert1 as c1
    g = {"tools": all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))}
    with tempfile.TemporaryDirectory() as tmp:
        cnf, prf, empty = (os.path.join(tmp, x) for x in ("php.cnf", "php.drat", "empty.drat"))
        nv, cls = c1.php(6, 5)
        c1.write_dimacs(cls, nv, cnf)
        res, _ = c1.run_cadical(tools, cnf, prf, 120)
        dr = c1.run_drat(tools, cnf, prf, 300) if res["status"] == "UNSAT" else {"verified": False}
        g["control_php65_verified"] = res["status"] == "UNSAT" and dr["verified"]
        open(empty, "w").close()
        g["control_empty_proof_rejected"] = not c1.run_drat(tools, cnf, empty, 120)["verified"]
        nv, cls = c1.php(5, 5)
        c1.write_dimacs(cls, nv, cnf)
        res, text = c1.run_cadical(tools, cnf, None, 120)
        g["control_php55_sat"] = res["status"] == "SAT" and c1.satisfied(cls, c1.model_of(text))
    with open(os.path.join(out_dir, "m95a_controls.json"), "w") as f:
        json.dump({"graded": g}, f, indent=1)
    print(f"SUMMARY controls all_match {all(g.values())} {json.dumps(g, sort_keys=True)}",
          flush=True)


# ---------- grading (pre-registered in m95-predictions.md) ----------

def load(out_dir, name):
    p = os.path.join(out_dir, name)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


def grade(group, out_dir):
    graded = {}
    st = load(out_dir, ORBITS_FILE) or {"graded": {"selfcheck": False}, "instances": {}}
    for key, ok in st["graded"].items():
        graded["selfcheck_" + key] = bool(ok)
    if group == "a":
        ctl = load(out_dir, "m95a_controls.json") or {"graded": {"controls": False}}
        graded.update(ctl["graded"])
    rows = load(out_dir, f"m95{group}_rows.json") or []
    sat = [r for r in rows if r["status"] == "SAT"]
    for r in sat:
        c = r["check"]
        graded["sat_" + r["name"]] = (c["system"] and c["anisotropic"] and c["shape"]
                                      and c["kept_hold"])
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    secs = [r["seconds"] for r in rows if r["status"] == "UNSAT"]
    out = {"group": group, "graded": graded, "instances": len(rows),
           "expected_instances": st["instances"].get(group), "counts": counts,
           "unsat_seconds_sum": round(sum(secs), 2),
           "unsat_seconds_median": statistics.median(secs) if secs else None,
           "unsat_seconds_max": max(secs, default=None),
           "slowest": max((r for r in rows if r["status"] == "UNSAT"),
                          key=lambda r: r["seconds"], default={}).get("name"),
           "not_unsat": [r["name"] for r in rows if r["status"] != "UNSAT"],
           "vars": sorted({(r.get("cnf") or {}).get("vars") for r in rows} - {None}),
           "clauses_range": [min(((r.get("cnf") or {}).get("clauses") or 0 for r in rows),
                                 default=None),
                             max(((r.get("cnf") or {}).get("clauses") or 0 for r in rows),
                                 default=None)]}
    if group == "a":
        done = [r for r in rows if r.get("cert") == "VERIFIED"]
        out.update({"verified": len(done),
                    "cadical_sum": round(sum(r["cadical"]["seconds"] for r in done), 2),
                    "drat_sum": round(sum(r["drat"]["seconds"] for r in done), 2),
                    "largest_proof": max((r["proof_bytes"] for r in done), default=None),
                    "not_verified": [r["name"] for r in rows if r.get("cert") != "VERIFIED"]})
        lad = load(out_dir, "m95a_ladder.json") or []
        for r in lad:
            if r["status"] == "SAT":
                c = r["check"]
                ok = c["system"] and c["shape"] and c["kept_hold"]
                # With the anisotropy clauses kept a model must be anisotropic; without them it
                # must not be, as the full CNF is UNSAT.
                graded["ladder_" + r["name"]] = ok and (c["anisotropic"] != bool(r.get("relax")))
        out["ladder"] = {r["name"]: [r["status"], r.get("seconds"), (r.get("cnf") or {}).get(
            "aniso_dropped"), (r.get("check") or {}).get("anisotropic")] for r in lad}
    out["rows"] = {r["name"]: [r["status"], r.get("seconds"), r.get("cert"),
                               (r.get("cadical") or {}).get("seconds"),
                               (r.get("drat") or {}).get("seconds"), r.get("proof_bytes"),
                               r.get("cnf_sha256")] for r in rows}
    return out


def summary_line(out):
    s = (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} graded "
         f"{len(out['graded'])} instances {out['instances']} expected "
         f"{out['expected_instances']} counts {json.dumps(out['counts'], sort_keys=True)} "
         f"not_unsat {out['not_unsat'][:12]} unsat_sum {out['unsat_seconds_sum']} median "
         f"{out['unsat_seconds_median']} max {out['unsat_seconds_max']} slowest {out['slowest']} "
         f"vars {out['vars'][:4]} clauses {out['clauses_range']}")
    if out["group"] == "a":
        s += (f" verified {out['verified']} not_verified {out['not_verified'][:8]} cadical_sum "
              f"{out['cadical_sum']} drat_sum {out['drat_sum']} largest_proof "
              f"{out['largest_proof']} ladder {json.dumps(out['ladder'], sort_keys=True)}")
    return s


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["selfcheck", "controls", "solve", "ladder", "child",
                                       "grade"], default="selfcheck")
    ap.add_argument("--group", choices=GROUPS, default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--cap-seconds", type=float, default=600.0)
    ap.add_argument("--minutes", type=float, default=110.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec", default="{}")
    ap.add_argument("--child-out", default="child.json")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "controls":
        run_controls(args.tools, args.out_dir)
    elif args.part == "solve":
        run_solve(args.group, args.tools, args.cap_seconds, args.minutes, args.out_dir)
    elif args.part == "ladder":
        run_ladder((args.cap_seconds, args.cap_seconds / 2), args.minutes, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, f"m95{args.group}_grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = selfcheck(args.out_dir)
        print(f"selfcheck: {json.dumps(st['graded'], sort_keys=True)} instances "
              f"{json.dumps(st['instances'])} sizes {json.dumps(st['sizes'])} seconds "
              f"{st['seconds']}", flush=True)
        print(f"SUMMARY selfcheck all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
