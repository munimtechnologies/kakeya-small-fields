# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m113: DRAT certificates for the 3,075 d = 1 cases with k(T(N)) <= 4 that jobs m110a-h and
m110j refuted (notes/a104.md, cube_groups/m113-predictions.md), each as the CNF that was UNSAT for
it: m106's "n" CNF (m102's relax CNF with anisotropy on the 15 non-zero vectors of N) for the 3,062
refuted at "n", m102's sweep CNF for the 13 refuted by the sweep at 120 s.

Why now: jobs m112a-l (the sweep CNF at 1,500 s on the 399 open cases) and the re-filed m110i are
still running. Whatever they decide, Proposition 40 (no case of the 34 d = 1 classes with k <= 4)
needs a checked certificate for every one of the 3,876 cases, as Propositions 38 and 39 had (jobs
m104 and m108: 1,172 of 1,172 VERIFIED). These 3,075 do not depend on m112, so they go first.

Parts:

    check     the grade files of m110a-h and j; the 3,075 cases with an UNSAT answer, by the CNF
              that was UNSAT (3,062 "n", 13 "sweep"); all d = 1 cases; this shard's share; the two
              programs present
    controls  cert1's three tool controls (as m104 and m108), and a positive control for this
              encoding: the "n" CNF of m110's d = 1 control o007_c008 t2_m012 (SAT at "n" in jobs
              m106b and m110a-j) written as DIMACS and solved by the CaDiCaL binary must be SAT,
              with a model that satisfies the CNF and passes m106's checks of the system
    cert      this shard's cases, two at a time, while time remains: CaDiCaL with an ASCII DRAT
              proof, drat-trim; the proof is deleted once checked
    grade     the graded checks of m113-predictions.md

Usage: python m113.py --part check|controls|cert|grade --shard a..f [--tools DIR] [--workers W]
       [--minutes M] [--out-dir D]
       (the grade files m110{a..h,j}_grade.json must be in the working directory)
"""
import argparse
import concurrent.futures as cf
import functools
import json
import os
import tempfile
import time

import m100
import m101
import m102
import m103
import m104
import m106
import m108
import m110
import m111
import sat_aniso as sa

T, D = m102.T, m102.D
M110_DONE = "abcdefghj"        # m110i was stopped from outside twice and is re-filed
SHARDS = "abcdef"
TOTAL = 3075                   # 3,489 cases of m110a-h, j minus the 414 left open (notes/a104.md)
BY_MODE = {"n": 3062, "sweep": 13}
# 3,075 = 6 * 512 + 3: shards a-c take 513 cases, d-f 512
SIZE = {s: 513 if s in "abc" else 512 for s in SHARDS}
CADICAL_CAP = 600.0
DRAT_CAP = {"n": 1200, "sweep": 1500}
CONTROL = m110.M106B_SAT       # r3b_t8_B7_o007_c008_t2_m012


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def tally(tab, key, status):
    tab.setdefault(key, {})
    tab[key][status] = tab[key].get(status, 0) + 1


# ---------- the cases ----------

@functools.lru_cache(maxsize=None)
def d1_cases():
    """{instance: (spec, case)} for the 3,876 d = 1 cases with k <= 4."""
    return {m102.inst_name(s, c): (s, c) for s, c in m110.sweep_cases()}


def mode_of(parts):
    """The CNF that was UNSAT for a case, from its {part: status} in m110's grade files: "n" if the
    "n" CNF was, else "sweep" if the sweep was, else None (the case is open)."""
    for mode in ("n", "sweep"):
        if parts.get(mode) == "UNSAT":
            return mode
    return None


def decided(parts):
    """[(instance, mode)] of the cases with an UNSAT answer, sorted by name."""
    out = ((x, mode_of(p)) for x, p in parts.items())
    return sorted((x, m) for x, m in out if m is not None)


def shard_of(i):
    return SHARDS[i % len(SHARDS)]


def shard_list(shard, items):
    return [x for i, x in enumerate(items) if shard_of(i) == shard]


# ---------- certify ----------

def certify(tools, spec, case, mode, tmp):
    """m108.certify_one with the mode given (and m113's caps): build exactly the CNF that was UNSAT,
    CaDiCaL with a DRAT proof, drat-trim. A SAT answer is checked against the CNF and the system."""
    inst = m102.inst_name(spec, case)
    inv, typ = m104.k_and_type(m103.space_of(case))
    row = {"instance": inst, "name": spec["name"], "kind": case["kind"], "maps": case["maps"],
           "dmeet": spec["dmeet"], "inv": inv, "type": typ, "mode": mode}
    path, prf = os.path.join(tmp, "i.cnf"), os.path.join(tmp, "i.drat")
    start = time.time()
    cnf, _ = m108.build_cert(spec, case, mode)
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
            row.update(check_sat(spec, case, mode, m104.model_of(text)))
    for p in (path, prf):
        if os.path.exists(p):
            os.remove(p)
    row["wall_seconds"] = round(time.time() - start, 2)
    return row


def check_sat(spec, case, mode, model):
    """A CaDiCaL model read back: does it satisfy the CNF, and (for "n") does it pass m106's checks
    (m101.check_model, m102.extra_checks, sigma != 0 on the vectors of N)?"""
    cnf, names = m108.build_cert(spec, case, mode)
    out = {"satisfies_cnf": m104.satisfied(cnf.clauses, model)}
    del cnf
    As, ss, B = sa.decode(model, names, T, D)
    res = {"A": As, "s": ss, "B": [[i, k, v] for (i, k), v in sorted(B.items())]}
    if mode == "n":
        chk = m101.check_model(spec, res)
        chk.update(m102.extra_checks(spec, case, res))
        _, sv = sa.tables(As, ss, B, D)
        chk["aniso_masks"] = all(sv[h] for h in m106.n_masks())
        out["check"] = chk
        out["verified"] = chk["aniso_masks"] and all(chk[k] for k in m102.needed(spec, "relax"))
    else:
        out["check"] = m100.check_model(spec, res)
    return out


def certify_item(tools, x, mode, deadline):
    """One case in its own temporary directory, or a SKIPPED row if the deadline has passed."""
    spec, case = d1_cases()[x]
    if time.time() > deadline:
        return {"instance": x, "name": spec["name"], "mode": mode, "cert": "SKIPPED"}
    with tempfile.TemporaryDirectory() as tmp:
        return certify(tools, spec, case, mode, tmp)


# ---------- the parts ----------

def run_check(shard, tools, out_dir):
    g, info = {}, {}
    parts = m111.m110_parts(M110_DONE)
    g["grades_loaded"] = parts is not None
    items = decided(parts or {})
    g["total_3075"] = len(items) == TOTAL
    by_mode = {}
    for _, m in items:
        by_mode[m] = by_mode.get(m, 0) + 1
    g["by_mode"] = by_mode == BY_MODE
    cases = d1_cases()
    g["names_d1"] = all(x in cases for x, _ in items)
    g["open_414"] = len(parts or {}) - len(items) == 414
    mine = shard_list(shard, items)
    g["shard_size"] = len(mine) == SIZE[shard]
    g["control_sat_at_n"] = (parts or {}).get(CONTROL, {}).get("n") == "SAT"
    g["tools"] = all(os.access(os.path.join(tools, x), os.X_OK) for x in ("cadical", "drat-trim"))
    info.update({"shard": mine, "by_mode": by_mode, "graded": g})
    save(out_dir, f"m113{shard}_check.json", info)
    bad = sorted(k for k, v in g.items() if not v)
    print(f"SUMMARY check {shard} all_match {not bad} graded {len(g)} failed {bad} "
          f"{json.dumps({'by_mode': by_mode, 'shard': len(mine)}, sort_keys=True)}", flush=True)


def run_controls(shard, tools, out_dir):
    """cert1's three tool controls (as m104.run_controls), then the positive control."""
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
    spec, case = d1_cases()[CONTROL]
    with tempfile.TemporaryDirectory() as tmp:
        row = certify(tools, spec, case, "n", tmp)
    g["control_n_sat"] = row["cert"] == "SAT"
    g["control_n_model"] = bool(row.get("satisfies_cnf")) and bool(row.get("verified"))
    g["control_n_d1"] = spec["dmeet"] == 1
    save(out_dir, f"m113{shard}_controls.json", {"graded": g, "row": row})
    print(f"SUMMARY controls {shard} all_match {all(g.values())} {json.dumps(g, sort_keys=True)} "
          f"clauses {row.get('clauses')} cadical {(row.get('cadical') or {}).get('seconds')} s",
          flush=True)


def run_cert(shard, tools, workers, minutes, out_dir):
    start = time.time()
    name = f"m113{shard}_cert.json"
    info = m100.load(out_dir, f"m113{shard}_check.json") or {"shard": []}
    rows, counts = [], {}
    d1_cases()                 # build the table once, before the threads start
    deadline = start + minutes * 60
    # CaDiCaL and drat-trim run as child processes (m104), so threads are enough
    with cf.ThreadPoolExecutor(max_workers=workers) as ex:
        futs = [ex.submit(certify_item, tools, x, mode, deadline) for x, mode in info["shard"]]
        for fut in cf.as_completed(futs):
            row = fut.result()
            rows.append(row)
            save(out_dir, name, rows)
            tally(counts, row.get("mode"), row["cert"])
            if row["cert"] != "SKIPPED":
                print(f"cert {row['instance']}: {row['cert']} {row['mode']} inv {row['inv']} "
                      f"{row['type']} cadical {row['cadical']['seconds']} s drat "
                      f"{(row.get('drat') or {}).get('seconds')} s proof {row['proof_bytes']} B "
                      f"clauses {row['clauses']}", flush=True)
    print(f"SUMMARY cert {shard} cases {len(rows)} {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade_rows(rows, mine):
    """(graded, out) for a shard from its cert rows and its [instance, mode] list."""
    g, out = {}, {}
    g["all_accounted"] = sorted([r["instance"], r["mode"]] for r in rows) == sorted(
        [x, m] for x, m in mine)
    done = [r for r in rows if r["cert"] != "SKIPPED"]
    g["no_sat"] = not any(r["cert"] == "SAT" for r in done)
    g["all_verified"] = all(r["cert"] == "VERIFIED" for r in done)
    # within one class, kind and mode the case only fixes unit clauses: same clause count
    sizes = {}
    for r in done:
        if "clauses" in r:
            sizes.setdefault((r["name"], r["kind"], r["mode"]), set()).add(r["clauses"])
    g["clauses_uniform"] = all(len(v) == 1 for v in sizes.values())
    by_mode, by_label = {}, {}
    for r in rows:
        tally(by_mode, r["mode"], r["cert"])
        tally(by_label, r["instance"][20:], r["cert"])

    def stats(key, mode):
        xs = sorted(r[key]["seconds"] for r in done if r["mode"] == mode and key in r)
        if not xs:
            return None
        return {"n": len(xs), "mean": round(sum(xs) / len(xs), 2), "median": xs[len(xs) // 2],
                "max": xs[-1]}

    out.update({"verified": sum(r["cert"] == "VERIFIED" for r in rows),
                "skipped": sorted(r["instance"] for r in rows if r["cert"] == "SKIPPED"),
                "not_verified": sorted([r["instance"], r["cert"]] for r in done
                                       if r["cert"] != "VERIFIED"),
                "by_mode": by_mode, "by_label": by_label,
                "cadical": {m: stats("cadical", m) for m in ("n", "sweep")},
                "drat": {m: stats("drat", m) for m in ("n", "sweep")},
                "largest_proof": max((r.get("proof_bytes", 0) for r in done), default=None),
                "rows": {r["instance"]: [r["cert"], r["mode"], r.get("inv"), r.get("type"),
                                         r.get("cnf_sha256"),
                                         (r.get("cadical") or {}).get("seconds"),
                                         (r.get("drat") or {}).get("seconds")]
                         for r in sorted(rows, key=lambda r: r["instance"])}})
    return g, out


def grade(shard, out_dir):
    g = {}
    for part in ("check", "controls"):
        st = m100.load(out_dir, f"m113{shard}_{part}.json")
        if st is None:
            g[part + "_ran"] = False
        else:
            g.update({part + "_" + k: v for k, v in st["graded"].items()})
    chk = m100.load(out_dir, f"m113{shard}_check.json") or {"shard": []}
    rows = m100.load(out_dir, f"m113{shard}_cert.json")
    g["cert_ran"] = rows is not None
    rg, out = grade_rows(rows or [], chk["shard"])
    g.update(rg)
    out["graded"] = g
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "controls", "cert", "grade"], default="check")
    ap.add_argument("--shard", choices=list(SHARDS), default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--minutes", type=float, default=210.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "check":
        run_check(args.shard, args.tools, args.out_dir)
    elif args.part == "controls":
        run_controls(args.shard, args.tools, args.out_dir)
    elif args.part == "cert":
        run_cert(args.shard, args.tools, args.workers, args.minutes, args.out_dir)
    else:
        out = grade(args.shard, args.out_dir)
        save(args.out_dir, f"m113{args.shard}_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        extra = {k: v for k, v in out.items() if k not in ("graded", "rows", "by_label")}
        print(f"SUMMARY grade {args.shard} all_match {not bad} graded {len(out['graded'])} failed "
              f"{bad[:12]} {json.dumps(extra, sort_keys=True)}", flush=True)


if __name__ == "__main__":
    main()
