# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m104: DRAT certificates for the 57 cases with at most 4 invariant subspaces in the three
d = 3 classes of the rank-0 case of (B7)_8 (t = 8, dim V = 11), the count of such cases in all 68
classes, and which anisotropy clauses a refutation needs (notes/a96.md,
cube_groups/m104-predictions.md).

What came back on 2026-10-24 (jobs m103a and m103b, notes/a96.md): every graded check held (28 of
28) and all six positive controls were SAT with verified models. In the three classes with d = 3,
every case whose commuting space T(N) leaves k <= 4 subspaces of Q = X / X_1 invariant was UNSAT
(57 of 57, with job m102's pilot). In o004_c000 (d = 2) it was 37 of 37, in o007_c008 (d = 1) 31 of
37, and in the two d = 0 classes 3 of 25. By m103's decision rules the 57 are certified before
they are counted, and the k <= 4 cases of all 68 classes are counted.

Parts:

    check    the 57 cases rebuilt from m102.class_cases and m103.describe, each answered UNSAT by
             job m102 or m103a; this shard's 19; the two programs present
    controls cert1's three tool controls (PHP(6, 5) VERIFIED, an empty proof rejected, PHP(5, 5)
             SAT with a model that satisfies every clause)
    cert     this shard's cases: m102's sweep CNF written as DIMACS, CaDiCaL with an ASCII DRAT
             proof, drat-trim on the proof (as cert1 and m98b); the proof is deleted once checked
    count    (shard a) every case of all 68 classes typed by k; the k <= 4 cases by class and by d
    core     (shard c) six certified-kind cases solved with no anisotropy clauses except those on a
             subspace W of V: W = N + span(the h with pi phi(h) != 0) ("out3", dim 7), that plus one
             more h ("out3_in1", dim 8), and N + the other four h ("in4", dim 8); a positive
             control first (o000_c000, t2 with M = J, W = N: the relax_n control of job m102)
    grade    the graded checks of m104-predictions.md

Usage: python m104.py --part check|controls|cert|count|core|grade --shard a|b|c [--tools DIR]
       [--cap-seconds S] [--minutes M] [--out-dir D]
"""
import argparse
import functools
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

import m42
import m100
import m101
import m102
import m103
import sat_aniso as sa

T, D, KD = m102.T, m102.D, m102.KD
X1_MASK = m102.X1_MASK
SHARDS = "abc"
D3 = [(0, 0), (1, 0), (2, 0)]          # (pair, class) of o000_c000, o001_c000, o002_c000
CADICAL_CAP = 600.0
DRAT_CAP = 1500
# job m103a (compete-results/m103a-b7-inv-v1, 2026-10-24): the cases of the d = 3 classes it answered
# UNSAT; job m102's pilot answers are m103.M102_PILOT
M103A_UNSAT = {
    "r3b_t8_B7_o000_c000": ["t2_m002", "t2_m074", "t2_m075", "t2_m076", "t2_m077", "t2_m078",
                            "t2_m079", "t2_m080", "t2_m085", "t2_m086", "t2_m087", "t2_m092",
                            "t2_m093", "t2_m094", "t2_m095", "t2_m096", "t2_m098", "t2_m099",
                            "t2_m104", "t2_m106", "t2_m107", "t2_m112"],
    "r3b_t8_B7_o001_c000": ["t2_m011", "t2_m012", "t2_m094", "t3_m001_176", "t3_m002_132",
                            "t3_m094_187"],
    "r3b_t8_B7_o002_c000": ["t2_m011", "t2_m012", "t2_m066", "t2_m067", "t2_m069", "t2_m071",
                            "t2_m092", "t2_m094", "t3_m001_176", "t3_m002_132", "t3_m004_034",
                            "t3_m011_017", "t3_m064_128", "t3_m064_136", "t3_m065_184",
                            "t3_m094_187"]}
CERT_BY_CLASS = {"r3b_t8_B7_o000_c000": 37, "r3b_t8_B7_o001_c000": 6, "r3b_t8_B7_o002_c000": 14}
# clause counts of the sweep CNFs in jobs m103a (by class and kind)
CLAUSES = {("r3b_t8_B7_o000_c000", "t2"): 907089, ("r3b_t8_B7_o000_c000", "t3"): 906081,
           ("r3b_t8_B7_o001_c000", "t2"): 907089, ("r3b_t8_B7_o001_c000", "t3"): 906081,
           ("r3b_t8_B7_o002_c000", "t2"): 907113, ("r3b_t8_B7_o002_c000", "t3"): 906105}
# job m102 (notes/a95.md): |Kbar| over the 68 classes, and the number of instances
A95_ORDERS = {1: 19, 2: 22, 3: 5, 4: 6, 6: 6, 7: 2, 8: 4, 24: 2, 168: 2}
A95_INSTANCES = 16272
# by hand (Lemmas 107 and 108): with Kbar trivial every space is its own orbit, and the spaces with
# k <= 4 are irr, nil3, x(x^2+x+1) (24 + 42 + 56) and F_8, F_2 x F_4, F_2[x]/(x^3) (8 + 28 + 21)
TRIVIAL_LE4 = 179
# job m103 (check part, "plan"): the k <= 4 cases of the classes it ran
M103_LE4 = {"r3b_t8_B7_o000_c000": 37, "r3b_t8_B7_o001_c000": 6, "r3b_t8_B7_o002_c000": 14,
            "r3b_t8_B7_o004_c000": 37, "r3b_t8_B7_o007_c008": 37, "r3b_t8_B7_o011_c000": 30,
            "r3b_t8_B7_o011_c005": 6}
# part core: (pair, class, label), one per type with k <= 4, each answered UNSAT by m102 or m103a
CORE = [(0, 0, "t3_m094_187"), (0, 0, "t2_m094"), (0, 0, "t3_m001_176"), (0, 0, "t2_m086"),
        (1, 0, "t3_m002_132"), (2, 0, "t2_m011")]
CORE_LEVELS = ("out3", "out3_in1", "in4")


# ---------- DIMACS and the two programs (as cert1.py) ----------

def write_dimacs(clauses, nv, path):
    """Writes the clauses as DIMACS CNF; returns the number of variables in the header."""
    nv = max([nv] + [abs(x) for c in clauses for x in c])
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    return nv


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def is_verified(text):
    """drat-trim's answer line: exactly 's VERIFIED' (not 's NOT VERIFIED')."""
    return any(line.strip() == "s VERIFIED" for line in text.splitlines())


def model_of(text):
    """The literals of CaDiCaL's 'v' lines."""
    return [int(x) for line in text.splitlines() if line.startswith("v ")
            for x in line.split()[1:] if x != "0"]


def satisfied(clauses, model):
    true = set(model)
    return all(any(x in true for x in c) for c in clauses)


def php(p, h):
    """The pigeonhole formula: p pigeons in h holes, at most one pigeon per hole."""
    v = lambda i, j: i * h + j + 1
    cls = [[v(i, j) for j in range(h)] for i in range(p)]
    cls += [[-v(i, j), -v(k, j)] for j in range(h) for i in range(p) for k in range(i + 1, p)]
    return p * h, cls


def run_cadical(tools, cnf_path, proof_path, cap=CADICAL_CAP):
    cmd = [os.path.join(tools, "cadical"), "-q", "--binary=0", cnf_path]
    if proof_path:
        cmd.append(proof_path)
    start = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                           timeout=cap)
    except subprocess.TimeoutExpired:
        return {"status": "UNKNOWN", "seconds": round(time.time() - start, 2)}, ""
    status = {20: "UNSAT", 10: "SAT"}.get(p.returncode, "ERROR")
    return {"status": status, "rc": p.returncode, "seconds": round(time.time() - start, 2)}, p.stdout


def run_drat(tools, cnf_path, proof_path, cap=DRAT_CAP):
    cmd = [os.path.join(tools, "drat-trim"), cnf_path, proof_path, "-t", str(int(cap))]
    start = time.time()
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
                           timeout=cap + 60)
    except subprocess.TimeoutExpired:
        return {"verified": False, "reason": "time limit", "seconds": round(time.time() - start, 2)}
    return {"verified": is_verified(p.stdout), "rc": p.returncode,
            "seconds": round(time.time() - start, 2),
            "tail": [x for x in p.stdout.splitlines() if x.strip()][-6:]}


# ---------- the cases ----------

def shard_of(i):
    return SHARDS[i % len(SHARDS)]


def known_unsat(name):
    return (set(m103.M102_PILOT.get(name, {}).get("UNSAT", []))
            | set(M103A_UNSAT.get(name, [])))


@functools.lru_cache(maxsize=None)
def k_and_type(space):
    return m103.inv_count(space), m103.alg_type(space)


def cert_cases():
    """[(spec, case)]: the k <= 4 cases of the three d = 3 classes, in m102's order."""
    out = []
    for pi, ci in D3:
        spec = m100.spec_of(pi, ci)
        out += [(spec, c) for c in m102.class_cases(spec)[1:]
                if k_and_type(m103.space_of(c))[0] <= 4]
    return out


def shard_cases(shard):
    return [x for i, x in enumerate(cert_cases()) if shard_of(i) == shard]


def w_masks(idx):
    """The non-zero vectors of span(e_i : i in idx), as bit masks of V."""
    wmask = sum(1 << i for i in idx)
    return [h for h in range(1, 1 << D) if h & ~wmask == 0]


def h_split(spec):
    """(the h_i with pi phi(h_i) != 0, the other h_i), as indices of the basis of V."""
    phis = m42.params(spec)[4]
    out = [i for i in range(KD, D) if phis[i] & ~X1_MASK]
    inside = [i for i in range(KD, D) if not phis[i] & ~X1_MASK]
    return out, inside


def level_idx(spec, level):
    out, inside = h_split(spec)
    extra = {"n": [], "out3": out, "out3_in1": out + inside[:1], "in4": inside}[level]
    return list(range(KD)) + extra


def core_items():
    """[(spec, case, level)]: the control first, then each core case at each level."""
    items = [(m100.spec_of(0, 0), m102.case_t2(m102.J3), "n")]
    for pi, ci, lab in CORE:
        spec = m100.spec_of(pi, ci)
        case = {m102.case_label(c): c for c in m102.class_cases(spec)}[lab]
        items += [(spec, case, lv) for lv in CORE_LEVELS]
    return items


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g = {}
    cases = cert_cases()
    labels = [(spec["name"], m102.case_label(c)) for spec, c in cases]
    g["cert_57"] = len(cases) == 57 and len(set(labels)) == 57
    g["cert_known_unsat"] = all(lab in known_unsat(name) for name, lab in labels)
    by_class = {}
    for name, _ in labels:
        by_class[name] = by_class.get(name, 0) + 1
    g["cert_by_class"] = by_class == CERT_BY_CLASS
    g["shard_19"] = len(shard_cases(shard)) == 19
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    info = {"shard": [f"{n}_{lab}" for i, (n, lab) in enumerate(labels) if shard_of(i) == shard]}
    if shard == "c":
        spec = m100.spec_of(0, 0)
        out, inside = h_split(spec)
        g["h_split_3_4"] = (len(out), len(inside)) == (3, 4)
        g["core_known_unsat"] = all(lab in known_unsat(m100.spec_of(pi, ci)["name"])
                                    for pi, ci, lab in CORE)
        kinds = {k_and_type(m103.space_of(c)) for _, c, _ in core_items()[1:]}
        g["core_types_le4"] = len(kinds) == len(CORE) and all(k <= 4 for k, _ in kinds)
        g["w_sizes"] = [len(w_masks(level_idx(spec, lv))) for lv in ("n",) + CORE_LEVELS] == [
            15, 127, 255, 255]
        info["h_split"] = [out, inside]
    info["graded"] = g
    save(out_dir, f"m104{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} by_class "
          f"{json.dumps(by_class, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    g = {}
    with tempfile.TemporaryDirectory() as tmp:
        cnf, prf, empty = (os.path.join(tmp, x) for x in ("php.cnf", "php.drat", "empty.drat"))
        nv, cls = php(6, 5)
        write_dimacs(cls, nv, cnf)
        res, _ = run_cadical(tools, cnf, prf, 120)
        dr = run_drat(tools, cnf, prf, 300) if res["status"] == "UNSAT" else {"verified": False}
        g["control_php65_verified"] = res["status"] == "UNSAT" and dr["verified"]
        open(empty, "w").close()
        g["control_empty_proof_rejected"] = not run_drat(tools, cnf, empty, 120)["verified"]
        nv, cls = php(5, 5)
        write_dimacs(cls, nv, cnf)
        res, text = run_cadical(tools, cnf, None, 120)
        g["control_php55_sat"] = res["status"] == "SAT" and satisfied(cls, model_of(text))
    save(out_dir, f"m104{shard}_controls.json", {"graded": g})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} {json.dumps(g, sort_keys=True)}",
          flush=True)


def check_cadical_model(spec, case, text):
    """A SAT answer of CaDiCaL read back: the CNF again, and the system outside the encoder."""
    cnf, names, _ = m102.build(spec, case, "sweep")
    model = model_of(text)
    out = {"satisfies_cnf": satisfied(cnf.clauses, model)}
    As, ss, B = sa.decode(model, names, T, D)
    res = {"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]}
    chk = m101.check_model(spec, res)
    chk.update(m102.extra_checks(spec, case, res))
    out["check"] = chk
    out["verified"] = out["satisfies_cnf"] and all(chk[k] for k in m102.needed(spec, "sweep"))
    return out


def certify_one(tools, spec, case, tmp):
    inv, typ = k_and_type(m103.space_of(case))
    row = {"instance": m102.inst_name(spec, case), "name": spec["name"], "kind": case["kind"],
           "maps": case["maps"], "dmeet": spec["dmeet"], "inv": inv, "type": typ}
    path, prf = os.path.join(tmp, "i.cnf"), os.path.join(tmp, "i.drat")
    start = time.time()
    cnf, _, _ = m102.build(spec, case, "sweep")
    row["clauses"] = len(cnf.clauses)
    row["vars"] = write_dimacs(cnf.clauses, cnf.nv, path)
    del cnf
    row["cnf_sha256"] = sha256(path)
    cad, text = run_cadical(tools, path, prf)
    row["cadical"] = cad
    row["proof_bytes"] = os.path.getsize(prf) if os.path.exists(prf) else 0
    if cad["status"] == "UNSAT":
        row["drat"] = run_drat(tools, path, prf)
        killed = (row["drat"].get("rc") in (-9, 137) or row["drat"].get("reason") == "time limit"
                  or any("timeout" in x.lower() for x in row["drat"].get("tail", [])))
        row["cert"] = ("VERIFIED" if row["drat"]["verified"]
                       else "DRAT_STOPPED" if killed else "NOT_VERIFIED")
    else:
        row["cert"] = cad["status"]
        if cad["status"] == "SAT":
            row["sat_check"] = check_cadical_model(spec, case, text)
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
        save(out_dir, f"m104{shard}_cert.json", rows)
        counts[row["cert"]] = counts.get(row["cert"], 0) + 1
        print(f"cert {row['instance']}: {row['cert']} inv {row.get('inv')} {row.get('type')} "
              f"cadical {(row.get('cadical') or {}).get('seconds')} s drat "
              f"{(row.get('drat') or {}).get('seconds')} s proof {row.get('proof_bytes')} B "
              f"clauses {row.get('clauses')}", flush=True)
    print(f"SUMMARY cert {shard} cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def run_count(out_dir):
    classes, orders, by_d = [], {}, {}
    for sh in sorted(m100.SHARDS):
        for spec in m100.shard_specs(sh):
            order = len(m102.kbar(spec))
            cases = m102.class_cases(spec)
            by_k = {}
            for c in cases[1:]:
                k = k_and_type(m103.space_of(c))[0]
                by_k[k] = by_k.get(k, 0) + 1
            le4 = sum(n for k, n in by_k.items() if k <= 4)
            classes.append({"name": spec["name"], "pair": spec["pair"], "cls": spec["cls"],
                            "dmeet": spec["dmeet"], "kbar_order": order,
                            "instances": len(cases), "le4": le4,
                            "by_k": {str(k): n for k, n in sorted(by_k.items())}})
            orders[order] = orders.get(order, 0) + 1
            by_d[spec["dmeet"]] = by_d.get(spec["dmeet"], 0) + le4
    total = sum(c["instances"] for c in classes)
    le4_all = sum(c["le4"] for c in classes)
    named = {c["name"]: c["le4"] for c in classes}
    g = {"classes_68": len(classes) == 68 and len(named) == 68,
         "instances_16272": total == A95_INSTANCES,
         "kbar_orders": orders == A95_ORDERS,
         "trivial_179": all(c["le4"] == TRIVIAL_LE4 for c in classes if c["kbar_order"] == 1),
         "m103_le4": all(named.get(n) == v for n, v in M103_LE4.items()),
         "d3_57": by_d.get(3) == 57}
    out = {"graded": g, "instances": total, "le4": le4_all,
           "le4_by_d": {str(d): n for d, n in sorted(by_d.items())},
           "hours_at_60s": round(le4_all * 60 / 3600, 1),
           "hours_at_45s_d2": round(by_d.get(2, 0) * 45 / 3600, 1),
           "kbar_orders": {str(k): n for k, n in sorted(orders.items())}, "classes": classes}
    save(out_dir, "m104_count.json", out)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY count all_match {not bad} graded {len(g)} failed {bad} instances {total} le4 "
          f"{le4_all} le4_by_d {json.dumps(out['le4_by_d'], sort_keys=True)} hours_at_60s "
          f"{out['hours_at_60s']} hours_at_45s_d2 {out['hours_at_45s_d2']}", flush=True)


def child(spec, case, idx, path):
    from pysat.solvers import Solver
    cnf, names, _ = m102.build(spec, case, "relax")
    n_aniso = m101.add_aniso_on(cnf, names, T, idx)
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
           "clauses": len(cnf.clauses), "aniso_clauses": n_aniso,
           "seconds": round(time.time() - start, 2)}
    if ok:
        As, ss, B = sa.decode(s.get_model(), names, T, D)
        res.update({"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]})
    s.delete()
    with open(path, "w") as f:
        json.dump(res, f)


def solve_core(spec, case, level, cap, out_dir):
    idx = level_idx(spec, level)
    tag = m102.inst_name(spec, case) + "_" + level
    path = os.path.join(out_dir, tag + ".child.json")
    cmd = [sys.executable, os.path.abspath(__file__), "--part", "child", "--spec", json.dumps(spec),
           "--case", json.dumps(case), "--idx", json.dumps(idx), "--child-out", path]
    start = time.time()
    try:
        subprocess.run(cmd, timeout=cap, check=True)
        with open(path) as f:
            res = json.load(f)
    except subprocess.TimeoutExpired:
        res = {"status": "UNKNOWN", "reason": "time budget reached"}
    except (subprocess.CalledProcessError, OSError, ValueError) as e:
        res = {"status": "ERROR", "reason": str(e)}
    inv, typ = k_and_type(m103.space_of(case))
    row = {k: v for k, v in res.items() if k not in ("A", "s", "B")}
    row.update({"instance": m102.inst_name(spec, case), "name": spec["name"], "level": level,
                "idx": idx, "kind": case["kind"], "maps": case["maps"], "inv": inv, "type": typ,
                "wall_seconds": round(time.time() - start, 2), "budget_seconds": cap})
    if res["status"] == "SAT":
        chk = m101.check_model(spec, res)
        chk.update(m102.extra_checks(spec, case, res))
        _, sv = sa.tables(res["A"], res["s"], {(i, k): v for i, k, v in res["B"]}, D)
        chk["aniso_w"] = all(sv[h] for h in w_masks(idx))
        row["check"] = chk
        row["verified"] = chk["aniso_w"] and all(chk[k] for k in m102.needed(spec, "relax"))
    print(f"core {tag}: {json.dumps(row, sort_keys=True)}", flush=True)
    return row


def run_core(cap, minutes, out_dir):
    start = time.time()
    rows, tab, skipped = [], {}, 0
    for spec, case, level in core_items():
        if time.time() - start > minutes * 60:
            skipped += 1
            continue
        row = solve_core(spec, case, level, cap, out_dir)
        rows.append(row)
        save(out_dir, "m104c_core.json", rows)
        key = f"{level} inv{row['inv']} {row['type']}"
        tab.setdefault(key, {})
        tab[key][row["status"]] = tab[key].get(row["status"], 0) + 1
    print(f"SUMMARY core skipped {skipped} {json.dumps(tab, sort_keys=True)} cap {cap}", flush=True)


def load(out_dir, name):
    p = os.path.join(out_dir, name)
    if not os.path.exists(p):
        return None
    with open(p) as f:
        return json.load(f)


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = load(out_dir, f"m104{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    rows = load(out_dir, f"m104{shard}_cert.json") or []
    g["cert_19"] = len(rows) == 19
    for r in rows:
        if r["cert"] != "SKIPPED":
            g["verified_" + r["instance"]] = r["cert"] == "VERIFIED"
            g["clauses_" + r["instance"]] = r["clauses"] == CLAUSES[(r["name"], r["kind"])]
    out = {"verified": sum(r["cert"] == "VERIFIED" for r in rows),
           "skipped": [r["instance"] for r in rows if r["cert"] == "SKIPPED"],
           "not_verified": [r["instance"] for r in rows if r["cert"] not in ("VERIFIED", "SKIPPED")],
           "cadical_sum": round(sum(r["cadical"]["seconds"] for r in rows if "cadical" in r), 2),
           "drat_sum": round(sum(r["drat"]["seconds"] for r in rows if "drat" in r), 2),
           "largest_proof": max((r.get("proof_bytes", 0) for r in rows), default=None),
           "rows": {r["instance"]: [r["cert"], r.get("inv"), r.get("type"), r.get("cnf_sha256"),
                                    (r.get("cadical") or {}).get("seconds"),
                                    (r.get("drat") or {}).get("seconds")] for r in rows}}
    if shard == "a":
        cnt = load(out_dir, "m104_count.json")
        if cnt is None:
            g["count_ran"] = False
        else:
            g.update({"count_" + k: v for k, v in cnt["graded"].items()})
            out["count"] = {k: cnt[k] for k in ("instances", "le4", "le4_by_d", "hours_at_60s",
                                                "hours_at_45s_d2")}
    if shard == "c":
        core = load(out_dir, "m104c_core.json") or []
        ctrl = [r for r in core if r["level"] == "n"]
        g["core_control_sat"] = bool(ctrl) and all(r["status"] == "SAT" and r.get("verified")
                                                   for r in ctrl)
        g["core_no_error"] = all(r["status"] in ("SAT", "UNSAT", "UNKNOWN") for r in core)
        for r in core:
            if r["status"] == "SAT":
                g[f"core_verified_{r['instance']}_{r['level']}"] = bool(r.get("verified"))
        out["core"] = {f"{r['instance']}_{r['level']}": [r["status"], r["wall_seconds"], r["inv"],
                                                         r["type"]] for r in core}
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "count", "core", "grade",
                                       "child"], default="check")
    ap.add_argument("--shard", choices=list(SHARDS), default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--cap-seconds", type=float, default=100.0)
    ap.add_argument("--minutes", type=float, default=100.0)
    ap.add_argument("--out-dir", default=".")
    ap.add_argument("--spec")
    ap.add_argument("--case")
    ap.add_argument("--idx")
    ap.add_argument("--child-out")
    args = ap.parse_args()
    if args.part == "child":
        child(json.loads(args.spec), json.loads(args.case), json.loads(args.idx), args.child_out)
        return
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.minutes, args.out_dir)
    elif args.part == "count":
        run_count(args.out_dir)
    elif args.part == "core":
        run_core(args.cap_seconds, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m104{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = f" count {json.dumps(out['count'], sort_keys=True)}" if "count" in out else ""
        if "core" in out:
            extra += f" core {json.dumps(out['core'], sort_keys=True)}"
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} verified {out['verified']} skipped {len(out['skipped'])} not_verified "
              f"{out['not_verified']} cadical_sum {out['cadical_sum']} drat_sum {out['drat_sum']} "
              f"largest_proof {out['largest_proof']}{extra}", flush=True)


if __name__ == "__main__":
    main()
