# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m108: DRAT certificates for the 1,115 cases with k(T(N)) <= 4 of the thirteen d = 2 classes
of the rank-0 case of (B7)_8 (t = 8, dim V = 11), and which equations of the system (*) the
contradiction "normal form + M" needs (notes/a100.md, cube_groups/m108-predictions.md).

What came back on 2026-10-25 (jobs m107a-f, notes/a100.md): every graded check held. The four d = 2
cases still open were UNSAT with anisotropy on N (147 to 218 s), so all 1,115 d = 2 cases with
k <= 4 are UNSAT (uncertified). In all ten core and k = 6 cases the deletion-minimal set of hand
conditions is {M} alone: the system (*), m42's normal form and A_(v_2), A_(v_3) = A_u-bar T pi
already contradict each other, and dropping M gives a verified model. With no anisotropy, 16 of the
56 cases with k = 6 of the d = 3 classes are UNSAT; every case with k = 8 or 10 is SAT.

The system (*) in coordinates (sat_aniso.coeff_ok), for basis indices i, j, k of V:

    (L)  A_j s_i = b(i, j) + A_i b(i, j)                  (b(i, i) = 0: A_i s_i = 0)
    (Q)  A_j b(i, k) + A_i b(k, j) + A_k b(i, j) = 0       (i < k, j not in {i, k})

Each index is u (index 0), v (v_1, v_2, v_3: 1..3) or h (h_1..h_7: 4..10). The equations of (L)
are grouped by (kind of i, kind of j), those of (Q) by the multiset of kinds of {i, j, k}: 9 + 7 = 16
groups (STAR). With all 16, encode_star is sat_aniso.encode(t, d, aniso=False, echelon=False)
clause for clause.

Parts:

    check    shards a-d: the 1,115 cases (m105.d2_specs, k <= 4) by class against job m104a's
             count, the four of m107a and the 28 of m106a among them, this shard's share, the two
             programs present; shards g, h: encode_star against sat_aniso.encode and the "M only"
             CNF against m107.build_groups(spec, case, ["M"]) (hashes), the group counts by hand
    controls shards a-d: cert1's three tool controls (as m104)
    cert     shards a-d: this shard's cases, each as the CNF that was UNSAT for it (m102's sweep CNF,
             or for the four of m107a the relax CNF with anisotropy on N), CaDiCaL with an ASCII
             DRAT proof, drat-trim; the proof is deleted once checked
    star     shard g: the six core cases; shard h: the four k = 6 cases, then twelve more k = 6
             cases that were UNSAT at "none" in m107b/c. A positive control first. With the normal
             form and M kept: all 16 groups, then (g, and the four of h) a deletion-minimal set of
             groups with the CNF still UNSAT (STAR_DROP)
    grade    the graded checks of m108-predictions.md

Usage: python m108.py --part check|controls|cert|star|grade --shard a|b|c|d|g|h
       [--tools DIR] [--cap-seconds S] [--minutes M] [--out-dir D]
"""
import argparse
import functools
import itertools
import json
import os
import subprocess
import sys
import tempfile
import time

import m42
import m100
import m102
import m103
import m104
import m105
import m106
import m107
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
CERT_SHARDS = "abcd"
CERT_TOTAL = 1115
# 1,115 = 4 * 278 + 3: shards a, b, c take 279 cases, d 278
CERT_SIZE = {"a": 279, "b": 279, "c": 279, "d": 278}
CADICAL_CAP = 900.0
DRAT_CAP = {"sweep": 1500, "n": 3000}
# the kind of each basis index of V: u, v_1..v_3, h_1..h_7
KIND = "u" + "v" * (KD - 1) + "h" * (D - KD)
ORDER = "uvh"
STAR = ("L_uu", "L_uv", "L_uh", "L_vu", "L_vv", "L_vh", "L_hu", "L_hv", "L_hh",
        "Q_uvv", "Q_uvh", "Q_uhh", "Q_vvv", "Q_vvh", "Q_vhh", "Q_hhh")
# drop the groups with most h first, so that what is kept is as small and as close to N as possible
STAR_DROP = ("Q_hhh", "Q_vhh", "Q_uhh", "L_hh", "Q_vvh", "Q_uvh", "L_hv", "L_vh", "L_hu", "L_uh",
             "Q_vvv", "Q_uvv", "L_vv", "L_vu", "L_uv", "L_uu")
# by hand, equations (one per row r of X, t = 8 rows): (L) n_a * n_b pairs (i, j) with n_u = 1,
# n_v = 3, n_h = 7; (Q) each 3-set {i, j, k} three times (once per choice of j)
STAR_COUNTS = {"L_uu": 8, "L_uv": 24, "L_uh": 56, "L_vu": 24, "L_vv": 72, "L_vh": 168, "L_hu": 56,
               "L_hv": 168, "L_hh": 392, "Q_uvv": 72, "Q_uvh": 504, "Q_uhh": 504, "Q_vvv": 24,
               "Q_vvh": 504, "Q_vhh": 1512, "Q_hhh": 840}
# job m107b/c (m107b_grade.json, m107c_grade.json): k = 6 cases UNSAT at "none", other than the
# four k = 6 items of m106/m107f
M_ONLY = ("r3b_t8_B7_o000_c000_t3_m006_161", "r3b_t8_B7_o000_c000_t3_m064_144",
          "r3b_t8_B7_o000_c000_t3_m072_161", "r3b_t8_B7_o000_c000_t2_m080",
          "r3b_t8_B7_o001_c000_t3_m002_004", "r3b_t8_B7_o002_c000_t3_m064_128",
          "r3b_t8_B7_o000_c000_t3_m001_160", "r3b_t8_B7_o000_c000_t3_m064_128",
          "r3b_t8_B7_o000_c000_t3_m072_145", "r3b_t8_B7_o000_c000_t3_m079_161",
          "r3b_t8_B7_o000_c000_t2_m112", "r3b_t8_B7_o002_c000_t3_m002_004")


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def append_row(out_dir, name, row):
    rows = m100.load(out_dir, name) or []
    rows.append(row)
    save(out_dir, name, rows)


# ---------- the groups of (*) ----------

def kinds(idx):
    return "".join(sorted((KIND[i] for i in idx), key=ORDER.index))


def l_group(i, j):
    """(L) with s_i and A_j."""
    return "L_" + KIND[i] + KIND[j]


def q_group(i, k, j):
    return "Q_" + kinds((i, k, j))


def count_groups(t=T, d=D):
    n = {g: 0 for g in STAR}
    for i in range(d):
        for j in range(d):
            n[l_group(i, j)] += t
    for i, k in itertools.combinations(range(d), 2):
        for j in range(d):
            if j not in (i, k):
                n[q_group(i, k, j)] += t
    return n


def encode_star(t, d, groups):
    """sat_aniso.encode(t, d, aniso=False, echelon=False) with only the equations of (*) in the
    given groups, in the same order (so with every group it is the same CNF). Returns (cnf, names,
    counts)."""
    groups = set(groups)
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
            g = l_group(i, j)
            if g not in groups:
                continue
            b = bv(i, j)
            for r in range(t):
                lits = prods(A[j], S[i], r)
                if b is not None:
                    lits += [b[r]] + prods(A[i], b, r)
                cnf.xor_eq(lits, 0)
                n[g] += 1
    for i, k in itertools.combinations(range(d), 2):
        for j in range(d):
            if j in (i, k):
                continue
            g = q_group(i, k, j)
            if g not in groups:
                continue
            for r in range(t):
                cnf.xor_eq(prods(A[j], bv(i, k), r) + prods(A[i], bv(k, j), r)
                           + prods(A[k], bv(i, j), r), 0)
                n[g] += 1
    return cnf, (A, S, B, None, None), n


def build_star(spec, case, groups):
    """(cnf, names, counts): the given groups of (*), m42's normal form (as m100.encode_fixed) and
    the case's maps M (as m102.build)."""
    t, d, au, s0, phis, kd, pvecs = m42.params(spec)
    cnf, names, counts = encode_star(t, d, groups)
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


def star_checks(As, ss, B, t, d):
    """Each group of (*) read back from (A_i, s_i, b(i, k)) as the equations it states."""
    ok = {g: True for g in STAR}

    def bv(i, k):
        return 0 if i == k else B[(min(i, k), max(i, k))]

    for i in range(d):
        for j in range(d):
            b = bv(i, j)
            if sa.mat_apply(As[j], ss[i], t) != b ^ sa.mat_apply(As[i], b, t):
                ok[l_group(i, j)] = False
    for i, k in itertools.combinations(range(d), 2):
        for j in range(d):
            if j in (i, k):
                continue
            if (sa.mat_apply(As[j], bv(i, k), t) ^ sa.mat_apply(As[i], bv(k, j), t)
                    ^ sa.mat_apply(As[k], bv(i, j), t)):
                ok[q_group(i, k, j)] = False
    return ok


def minimize(oracle, order):
    """A deletion-minimal set of groups (in the given order) for which oracle(list) is 'UNSAT', or
    None if all of them together are not. Returns (kept, why_kept, log): a kept group's removal gave
    a status other than UNSAT (SAT proves it is needed; UNKNOWN or SKIPPED does not)."""
    cur = list(order)
    log = [[None, oracle(cur)]]
    if log[0][1] != "UNSAT":
        return None, {}, log
    why = {}
    for g in order:
        trial = [x for x in cur if x != g]
        st = oracle(trial)
        log.append([g, st])
        if st == "UNSAT":
            cur = trial
        else:
            why[g] = st
    return [g for g in order if g in cur], why, log


# ---------- the cases ----------

@functools.lru_cache(maxsize=None)
def cert_cases():
    """((spec, case), ...): the k <= 4 cases of the 13 d = 2 classes, in m102's order."""
    out = []
    for spec in m105.d2_specs():
        out += [(spec, c) for c in m102.class_cases(spec)[1:] if m105.le4(c)]
    return tuple(out)


def shard_of(i):
    return CERT_SHARDS[i % len(CERT_SHARDS)]


def shard_cases(shard):
    return [x for i, x in enumerate(cert_cases()) if shard_of(i) == shard]


def mode_of(instance):
    """The CNF that was UNSAT for the case: anisotropy on N for m107a's four, else m102's sweep."""
    return "n" if instance in m107.OPEN_D2 else "sweep"


def build_cert(spec, case, mode):
    if mode == "sweep":
        cnf, names, _ = m102.build(spec, case, "sweep")
    else:
        cnf, names, _ = m102.build(spec, case, "relax")
        m106.add_aniso_masks(cnf, names, T, m106.n_masks())
    return cnf, names


def star_items(shard):
    """[(spec, case, part)]: g the six core cases; h the four k = 6 cases, then M_ONLY."""
    items = m106.min_items()
    if shard == "g":
        return [x for x in items if x[2] == "core"]
    return [x for x in items if x[2] == "k6"] + [m106.case_of(x) + ("m_only",) for x in M_ONLY]


# ---------- part cert ----------

def certify_one(tools, spec, case, tmp):
    inst = m102.inst_name(spec, case)
    mode = mode_of(inst)
    inv, typ = m104.k_and_type(m103.space_of(case))
    row = {"instance": inst, "name": spec["name"], "kind": case["kind"], "maps": case["maps"],
           "dmeet": spec["dmeet"], "inv": inv, "type": typ, "mode": mode}
    path, prf = os.path.join(tmp, "i.cnf"), os.path.join(tmp, "i.drat")
    start = time.time()
    cnf, _ = build_cert(spec, case, mode)
    row["clauses"] = len(cnf.clauses)
    row["vars"] = m104.write_dimacs(cnf.clauses, cnf.nv, path)
    del cnf
    row["cnf_sha256"] = m104.sha256(path)
    cad, text = m104.run_cadical(tools, path, prf, CADICAL_CAP)
    row["cadical"] = cad
    row["proof_bytes"] = os.path.getsize(prf) if os.path.exists(prf) else 0
    if cad["status"] == "UNSAT":
        row["drat"] = m104.run_drat(tools, path, prf, DRAT_CAP[mode])
        killed = (row["drat"].get("rc") in (-9, 137) or row["drat"].get("reason") == "time limit"
                  or any("timeout" in x.lower() for x in row["drat"].get("tail", [])))
        row["cert"] = ("VERIFIED" if row["drat"]["verified"]
                       else "DRAT_STOPPED" if killed else "NOT_VERIFIED")
    else:
        row["cert"] = cad["status"]
        if cad["status"] == "SAT":
            cnf, names = build_cert(spec, case, mode)
            model = m104.model_of(text)
            row["satisfies_cnf"] = m104.satisfied(cnf.clauses, model)
            As, ss, B = sa.decode(model, names, T, D)
            res = {"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]}
            row["check"] = m100.check_model(spec, res)
            del cnf
    for p in (path, prf):
        if os.path.exists(p):
            os.remove(p)
    row["wall_seconds"] = round(time.time() - start, 2)
    return row


def run_cert(shard, tools, minutes, out_dir):
    start = time.time()
    rows, counts = [], {}
    for spec, case in shard_cases(shard):
        if time.time() - start > minutes * 60:
            row = {"instance": m102.inst_name(spec, case), "name": spec["name"], "cert": "SKIPPED"}
        else:
            with tempfile.TemporaryDirectory() as tmp:
                row = certify_one(tools, spec, case, tmp)
        rows.append(row)
        save(out_dir, f"m108{shard}_cert.json", rows)
        counts[row["cert"]] = counts.get(row["cert"], 0) + 1
        print(f"cert {row['instance']}: {row['cert']} {row.get('mode')} inv {row.get('inv')} "
              f"{row.get('type')} cadical {(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"clauses {row.get('clauses')}", flush=True)
    print(f"SUMMARY cert {shard} cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def run_controls(shard, tools, out_dir):
    """cert1's three tool controls, as m104.run_controls."""
    g = {}
    with tempfile.TemporaryDirectory() as tmp:
        cnf, prf, empty = (os.path.join(tmp, x) for x in ("php.cnf", "php.drat", "empty.drat"))
        nv, cls = m104.php(6, 5)
        m104.write_dimacs(cls, nv, cnf)
        res, _ = m104.run_cadical(tools, cnf, prf, 120)
        dr = m104.run_drat(tools, cnf, prf, 300) if res["status"] == "UNSAT" else {"verified": False}
        g["control_php65_verified"] = res["status"] == "UNSAT" and dr["verified"]
        open(empty, "w").close()
        g["control_empty_proof_rejected"] = not m104.run_drat(tools, cnf, empty, 120)["verified"]
        nv, cls = m104.php(5, 5)
        m104.write_dimacs(cls, nv, cnf)
        res, text = m104.run_cadical(tools, cnf, None, 120)
        g["control_php55_sat"] = res["status"] == "SAT" and m104.satisfied(cls, m104.model_of(text))
    save(out_dir, f"m108{shard}_controls.json", {"graded": g})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} {json.dumps(g, sort_keys=True)}",
          flush=True)


# ---------- part star ----------

def child(spec, case, groups, path):
    from pysat.solvers import Solver
    cnf, names, counts = build_star(spec, case, groups)
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


def solve_star(spec, case, groups, tag, part, cap, out_dir):
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--groups", json.dumps(list(groups)), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    inv, typ = m104.k_and_type(m103.space_of(case))
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "tag": tag,
                "part": part, "groups": [g for g in STAR if g in groups], "kind": case["kind"],
                "maps": case["maps"], "dmeet": spec["dmeet"], "inv": inv, "type": typ,
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        B = {(i, k): v for i, k, v in res["B"]}
        star = star_checks(res["A"], res["s"], B, T, D)
        chk = m100.check_model(spec, res)
        chk["t_maps"] = m102.extra_checks(spec, case, res)["t_maps"]
        row["check"] = {k: chk[k] for k in ("system", "normal_form", "anisotropic", "t_maps")}
        row["verified"] = (chk["normal_form"] and chk["t_maps"]
                           and all(star[g] for g in groups))
        row["violated"] = [g for g in STAR if not star[g]]
    print(f"solve {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def run_star(shard, cap, minutes, out_dir):
    start = time.time()
    name = f"m108{shard}_rows.json"
    spec, case = m106.transfer_controls()[0]
    x = m102.inst_name(spec, case)
    append_row(out_dir, name, solve_star(spec, case, STAR, f"{x}_all", "control", cap, out_dir))
    mins, skipped = [], []
    for spec, case, part in star_items(shard):
        x = m102.inst_name(spec, case)
        if part == "m_only":
            if time.time() - start > minutes * 60:
                skipped.append(x)
                continue
            append_row(out_dir, name, solve_star(spec, case, STAR, f"{x}_all", part, cap, out_dir))
            continue
        step = [0]

        def oracle(groups):
            if time.time() - start > minutes * 60:
                return "SKIPPED"
            step[0] += 1
            row = solve_star(spec, case, groups, f"{x}_s{step[0]:02d}", part, cap, out_dir)
            append_row(out_dir, name, row)
            return row["status"]

        kept, why, log = minimize(oracle, STAR_DROP)
        entry = {"instance": x, "part": part, "type": m104.k_and_type(m103.space_of(case))[1],
                 "kept": kept, "why": why, "log": log}
        mins.append(entry)
        save(out_dir, f"m108{shard}_min.json", mins)
        print(f"min {x}: {json.dumps(entry, sort_keys=True)}", flush=True)
    save(out_dir, f"m108{shard}_skipped.json", skipped)
    short = {e["instance"][10:]: e["kept"] for e in mins}
    print(f"SUMMARY run {shard} skipped {len(skipped)} {json.dumps(short, sort_keys=True)}",
          flush=True)


# ---------- check and grade ----------

def run_check(shard, tools, out_dir):
    g, info = {}, {}
    if shard in CERT_SHARDS:
        cases = cert_cases()
        names = [m102.inst_name(s, c) for s, c in cases]
        by_class = {}
        for s, _ in cases:
            by_class[s["name"]] = by_class.get(s["name"], 0) + 1
        g["cert_1115"] = len(cases) == CERT_TOTAL and len(set(names)) == CERT_TOTAL
        g["by_class"] = by_class == m105.D2_LE4
        g["all_d2_le4"] = all(s["dmeet"] == 2 and m105.le4(c) for s, c in cases)
        g["open_and_m106a_inside"] = set(m107.OPEN_D2) | set(m106.UNKNOWN_D2) <= set(names)
        g["shard_size"] = len(shard_cases(shard)) == CERT_SIZE[shard]
        g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK)
                         for x in ("cadical", "drat-trim"))
        info["shard"] = [x for i, x in enumerate(names) if shard_of(i) == shard]
        info["n_mode"] = [x for x in info["shard"] if mode_of(x) == "n"]
    else:
        ref, _ = sa.encode(T, D, aniso=False, echelon=False)
        cnf, _, counts = encode_star(T, D, STAR)
        g["star_same_as_encode"] = ((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv)
                                    == (m100.clause_hash(ref), len(ref.clauses), ref.nv))
        g["star_counts_by_hand"] = counts == STAR_COUNTS == count_groups()
        del ref, cnf
        items = star_items(shard)
        spec, case, _ = items[0]
        ref, _, _ = m107.build_groups(spec, case, ["M"])
        cnf, _, counts = build_star(spec, case, STAR)
        g["m_only_same_as_m107"] = ((m100.clause_hash(cnf), len(cnf.clauses), cnf.nv)
                                    == (m100.clause_hash(ref), len(ref.clauses), ref.nv))
        g["m_counts"] = counts["M"] == 128
        info["clauses"] = len(cnf.clauses)
        del ref, cnf
        g["items"] = len(items) == (6 if shard == "g" else 16)
        if shard == "h":
            g["m_only_k6_d3"] = all(m104.k_and_type(m103.space_of(c))[0] == 6 and s["dmeet"] == 3
                                    for s, c, p in items if p == "m_only")
        info["items"] = [m102.inst_name(s, c) for s, c, _ in items]
    info["graded"] = g
    save(out_dir, f"m108{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({k: v for k, v in info.items() if k not in ('graded', 'shard')}, sort_keys=True)}",
          flush=True)


def grade(shard, out_dir):
    g, out = {}, {}
    parts = ("check", "controls") if shard in CERT_SHARDS else ("check",)
    for part in parts:
        st = m100.load(out_dir, f"m108{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    if shard in CERT_SHARDS:
        rows = m100.load(out_dir, f"m108{shard}_cert.json") or []
        g["cert_rows"] = len(rows) == CERT_SIZE[shard]
        for r in rows:
            if r["cert"] != "SKIPPED":
                g["verified_" + r["instance"]] = r["cert"] == "VERIFIED"
        # within one class, kind and mode the case only fixes unit clauses: same clause count
        sizes = {}
        for r in rows:
            if "clauses" in r:
                sizes.setdefault((r["name"], r["kind"], r["mode"]), set()).add(r["clauses"])
        g["clauses_uniform"] = all(len(v) == 1 for v in sizes.values())
        out.update({"verified": sum(r["cert"] == "VERIFIED" for r in rows),
                    "skipped": [r["instance"] for r in rows if r["cert"] == "SKIPPED"],
                    "not_verified": [[r["instance"], r["cert"]] for r in rows
                                     if r["cert"] not in ("VERIFIED", "SKIPPED")],
                    "sat": [r["instance"] for r in rows if r["cert"] == "SAT"],
                    "cadical_sum": round(sum(r["cadical"]["seconds"] for r in rows
                                             if "cadical" in r), 2),
                    "drat_sum": round(sum(r["drat"]["seconds"] for r in rows if "drat" in r), 2),
                    "largest_proof": max((r.get("proof_bytes", 0) for r in rows), default=None),
                    "rows": {r["instance"]: [r["cert"], r.get("mode"), r.get("inv"), r.get("type"),
                                             r.get("cnf_sha256"),
                                             (r.get("cadical") or {}).get("seconds"),
                                             (r.get("drat") or {}).get("seconds")] for r in rows}})
    else:
        rows = m100.load(out_dir, f"m108{shard}_rows.json") or []
        g["no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in rows)
        for r in rows:
            if r["status"] == "SAT":
                g[f"verified_{r['tag']}"] = bool(r.get("verified"))
        ctrl = [r for r in rows if r["part"] == "control"]
        g["control_sat"] = len(ctrl) == 1 and ctrl[0]["status"] == "SAT" and bool(
            ctrl[0].get("verified"))
        mins = m100.load(out_dir, f"m108{shard}_min.json") or []
        g["min_ran"] = len(mins) == (6 if shard == "g" else 4)
        # all 16 groups with M is the "M only" CNF of m107e/f, UNSAT for every one of these cases
        g["all_groups_unsat"] = bool(mins) and all(e["log"][0][1] == "UNSAT" for e in mins)
        out["full_models"] = sorted(r["tag"] for r in rows if r["status"] == "SAT"
                                    and r["check"].get("anisotropic"))
        out["min"] = {e["instance"][10:]: {"kept": e["kept"], "proven": m106.proven(e),
                                           "why": e["why"], "type": e["type"]} for e in mins}
        out["violated"] = {r["tag"]: r["violated"] for r in rows
                           if r["status"] == "SAT" and r["part"] != "control"}
        if shard == "h":
            only = [r for r in rows if r["part"] == "m_only"]
            out["m_only"] = {r["instance"][10:]: [r["status"], r["wall_seconds"], r["type"]]
                             for r in only}
            out["m_only_tally"] = {}
            for r in only:
                tally(out["m_only_tally"], r["type"], r["status"])
            out["skipped"] = m100.load(out_dir, f"m108{shard}_skipped.json") or []
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "star", "grade", "child"],
                    default="check")
    ap.add_argument("--shard", choices=list(CERT_SHARDS + "gh"), default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--cap-seconds", type=float, default=120.0)
    ap.add_argument("--minutes", type=float, default=200.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--groups")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), json.loads(args.groups), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.minutes, args.out_dir)
    elif args.part == "star":
        run_star(args.shard, args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m108{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "m_only")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
