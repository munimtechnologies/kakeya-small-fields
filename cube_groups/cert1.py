# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job cert1: a first pilot of proof certificates for the UNSAT answers behind (B6)
(cube_groups/cert1-predictions.md; notes/a76.md).

Every UNSAT answer in the notes so far is a solver answer saved without a proof certificate. This
job rebuilds a sample of the split instances of one class with the very same code that ran them,
solves each with a standalone CaDiCaL that writes a DRAT proof, and checks every proof with
drat-trim, an independent proof checker. A VERIFIED answer means: this CNF has no solution, checked
clause by clause. It does not check the encoding, the hints, Lemma 93 or Proposition 33.

The class: r3b_t7_B6_o005_c003 (d = 2), closed by jobs m88a-v2 and m90 (Corollary 115). Its 1961
split instances are m69.py's, in m66's order; the rank-0 ones carry Lemma 93 (b), as when they ran.
The sample, fixed before the job ran: every 20th, k = 0, 20, ..., 1960 (99 instances). Three of
them (a0060 of rank 1, a0240 and a1960 of rank 0) are among the 32 that m88a-v2 left open and m90
closed in 27 to 66 s, so the sample has some hard instances in it.

The instances are built by m69.py, m66.py, m58.py, m57.py and sat_aniso.py, imported unchanged; the
class gate and the re-run rows are m90.py's. CaDiCaL and drat-trim are built from their published
sources by cert1_tools.py.

Parts:
    check    graded: both programs present; the controls (the pigeonhole formula PHP(6, 5) solved
             UNSAT by CaDiCaL with its proof VERIFIED by drat-trim, the same formula with an empty
             proof not VERIFIED, PHP(5, 5) solved SAT with a model that satisfies every clause); the
             class against m66's run (m90's gate) and its roots recomputed; the sample (99, in
             range, the three re-runs in it equal to m90's rows); hint and unit counts of the first
             instance of rank 0 and of the first of another rank; the first instance written as
             DIMACS and read back unchanged. Writes cert1_specs.json and check.json.
    certify  each sample instance in order: DIMACS, CaDiCaL with an ASCII DRAT proof, drat-trim
             on the proof; the proof is deleted after it is checked (it can be rebuilt).
    grade    counts and times; which instances are not VERIFIED.

Usage: python cert1.py --part check|certify|grade [--tools tools] [--minutes 120] [--out-dir DIR]
"""
import argparse
import hashlib
import json
import os
import random
import statistics
import subprocess
import tempfile
import time

import m90
import m69 as b
import m57 as m

NAME = "r3b_t7_B6_o005_c003"
STEP = 20
SAMPLE = tuple(range(0, m90.NAMED_GATE[NAME]["orbits"], STEP))
RERUN_IN_SAMPLE = (60, 240, 1960)
CADICAL_CAP = 400.0
DRAT_CAP = 1200
SPECS_FILE = "cert1_specs.json"


# ---------- DIMACS and the two programs ----------

def write_dimacs(clauses, nv, path):
    """Writes the clauses as DIMACS CNF; returns the number of variables in the header."""
    nv = max([nv] + [abs(x) for c in clauses for x in c])
    with open(path, "w") as f:
        f.write(f"p cnf {nv} {len(clauses)}\n")
        for c in clauses:
            f.write(" ".join(map(str, c)) + " 0\n")
    return nv


def read_dimacs(path):
    """(nv, clauses) of a DIMACS file written by write_dimacs."""
    nv, clauses, cur = 0, [], []
    with open(path) as f:
        for line in f:
            if line.startswith("c"):
                continue
            if line.startswith("p"):
                nv = int(line.split()[2])
                continue
            for x in map(int, line.split()):
                if x == 0:
                    clauses.append(cur)
                    cur = []
                else:
                    cur.append(x)
    return nv, clauses


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


# ---------- the sample ----------

def sample_specs(reps):
    """m69's split instance at each sampled root, with Lemma 93 (b) when of rank 0 on X_1."""
    return [b.split_spec(NAME, k, reps[k], reps[k]["rank_x1"] == 0) for k in SAMPLE]


def rerun_rows():
    """m90's re-run rows of the class by k: (class, k, rank on X_1, m66 index, size, A_(v_1))."""
    return {row[1]: row for g in ("a", "b") for row in m90.OPEN_PREV[g] if row[0] == NAME}


def sample_ok(specs):
    rows = rerun_rows()
    by_k = dict(zip(SAMPLE, specs))
    return (len(SAMPLE) == len(specs) == 99 and SAMPLE[-1] == 1960
            and tuple(sorted(k for k in rows if k % STEP == 0)) == RERUN_IN_SAMPLE
            and len({sp["name"] for sp in specs}) == len(specs)
            and all(sp["parent"] == NAME and bool(sp.get("lemma93")) == (sp["rank_x1"] == 0)
                    and sp["name"] == m90.named_name(NAME, k, sp["rank_x1"])
                    for k, sp in by_k.items())
            and all(by_k[k]["m66_index"] == rows[k][3] and by_k[k]["size"] == rows[k][4]
                    and by_k[k]["a1"] == rows[k][5] and by_k[k]["rank_x1"] == rows[k][2]
                    for k in RERUN_IN_SAMPLE))


# ---------- parts ----------

def check(tools, out_dir):
    start = time.time()
    graded, probes = {}, {}
    graded["tools"] = all(os.access(os.path.join(tools, x), os.X_OK)
                          for x in ("cadical", "drat-trim"))
    with tempfile.TemporaryDirectory() as tmp:
        cnf, prf, empty = (os.path.join(tmp, x) for x in ("php.cnf", "php.drat", "empty.drat"))
        write_dimacs(php(6, 5)[1], php(6, 5)[0], cnf)
        res, _ = run_cadical(tools, cnf, prf, 120)
        dr = run_drat(tools, cnf, prf, 300) if res["status"] == "UNSAT" else {"verified": False}
        probes["php65"] = [res, dr]
        graded["control_php65_verified"] = res["status"] == "UNSAT" and dr["verified"]
        open(empty, "w").close()
        de = run_drat(tools, cnf, empty, 120)
        probes["php65_empty_proof"] = de
        graded["control_empty_proof_rejected"] = not de["verified"]
        nv, cls = php(5, 5)
        write_dimacs(cls, nv, cnf)
        res, text = run_cadical(tools, cnf, None, 120)
        probes["php55"] = res
        graded["control_php55_sat"] = res["status"] == "SAT" and satisfied(cls, model_of(text))
    gate = m90.NAMED_GATE[NAME]
    r, rr = b.class_reps(NAME, random.Random(90))
    graded["class"] = m90.class_ok(r, gate)
    graded["class_reps"] = m90.reps_ok(NAME, rr, gate)
    specs = sample_specs(rr)
    graded["sample"] = sample_ok(specs)
    first_l = next(sp for sp in specs if sp.get("lemma93"))
    first_s = next(sp for sp in specs if not sp.get("lemma93"))
    for tag, sp, units in (("l", first_l, m.T * m.T + 21), ("s", first_s, m.T * m.T)):
        c, _, h, u = m.build(dict(sp), "cadical")
        probes["build_" + tag] = [sp["name"], c.nv, len(c.clauses), h, u]
        graded["build_" + tag] = h == m.HAND_HINTS["B6"] and u == units and m.units_consistent(c)
    c, _, _, _ = m.build(dict(specs[0]), "cadical")
    with tempfile.TemporaryDirectory() as tmp:
        path = os.path.join(tmp, "x.cnf")
        nv = write_dimacs(c.clauses, c.nv, path)
        graded["dimacs_roundtrip"] = (read_dimacs(path) == (nv, [list(x) for x in c.clauses])
                                      and nv == c.nv)
    with open(os.path.join(out_dir, SPECS_FILE), "w") as f:
        json.dump(specs, f)
    st = {"graded": graded, "probes": probes, "sample": len(specs),
          "ranks": {str(k): sum(sp["rank_x1"] == k for sp in specs) for k in (0, 1, 2)},
          "seconds": round(time.time() - start, 1)}
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(st, f, indent=1)
    return st


def certify_one(tools, sp, tmp):
    c, _, h, u = m.build(dict(sp), "cadical")
    cnf, prf = os.path.join(tmp, "i.cnf"), os.path.join(tmp, "i.drat")
    nv = write_dimacs(c.clauses, c.nv, cnf)
    out = {"name": sp["name"], "rank_x1": sp["rank_x1"], "lemma93": bool(sp.get("lemma93")),
           "vars": nv, "clauses": len(c.clauses), "hints": h, "units": u, "cnf_sha256": sha256(cnf)}
    res, _ = run_cadical(tools, cnf, prf)
    out["cadical"] = res
    out["proof_bytes"] = os.path.getsize(prf) if os.path.exists(prf) else 0
    out["drat"] = run_drat(tools, cnf, prf) if res["status"] == "UNSAT" else None
    out["status"] = ("VERIFIED" if out["drat"] and out["drat"]["verified"]
                     else res["status"] if res["status"] != "UNSAT" else "NOT_VERIFIED")
    for p in (cnf, prf):
        if os.path.exists(p):
            os.remove(p)
    return out


def certify(tools, minutes, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing certified")
    with open(os.path.join(out_dir, SPECS_FILE)) as f:
        specs = json.load(f)
    counts = {}
    with tempfile.TemporaryDirectory() as tmp:
        for sp in specs:
            if time.time() - start > minutes * 60:
                out = {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "SKIPPED"}
            else:
                out = certify_one(tools, sp, tmp)
            with open(os.path.join(out_dir, f"cert1_{sp['name']}.json"), "w") as f:
                json.dump(out, f, indent=1)
            counts[out["status"]] = counts.get(out["status"], 0) + 1
            print(f"certify {sp['name']}: {out['status']} cadical "
                  f"{out.get('cadical', {}).get('seconds')} s drat "
                  f"{(out.get('drat') or {}).get('seconds')} s proof {out.get('proof_bytes')} B",
                  flush=True)
    print(f"SUMMARY certify {json.dumps(counts, sort_keys=True)}", flush=True)


def grade(out_dir):
    with open(os.path.join(out_dir, "check.json")) as f:
        graded = json.load(f)["graded"]
    with open(os.path.join(out_dir, SPECS_FILE)) as f:
        specs = json.load(f)
    rows = []
    for sp in specs:
        p = os.path.join(out_dir, f"cert1_{sp['name']}.json")
        rows.append(json.load(open(p)) if os.path.exists(p) else
                    {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "MISSING"})
    done = [r for r in rows if r["status"] == "VERIFIED"]
    cad = [r["cadical"]["seconds"] for r in done]
    drt = [r["drat"]["seconds"] for r in done]
    big = max(done, key=lambda r: r["proof_bytes"], default=None)
    out = {"class": NAME, "graded": graded, "sample": len(specs),
           "status": {r["name"]: r["status"] for r in rows},
           "verified": len(done), "not_verified": [r["name"] for r in rows
                                                   if r["status"] != "VERIFIED"],
           "any_sat": any(r["status"] == "SAT" for r in rows),
           "cadical_sum": round(sum(cad), 2), "drat_sum": round(sum(drt), 2),
           "cadical_median": statistics.median(cad) if cad else None,
           "drat_median": statistics.median(drt) if drt else None,
           "cadical_max": max(cad, default=None), "drat_max": max(drt, default=None),
           "largest_proof": [big["name"], big["proof_bytes"]] if big else None,
           "reruns": {r["name"]: [r["status"], r.get("cadical", {}).get("seconds"),
                                  (r.get("drat") or {}).get("seconds"), r.get("proof_bytes")]
                      for r in rows if int(r["name"][-4:]) in RERUN_IN_SAMPLE}}
    tj = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools", "tools.json")
    if os.path.exists(tj):
        out["tools"] = json.load(open(tj))
    return out


def summary_line(out):
    return (f"SUMMARY grade all_match {all(out['graded'].values())} graded {len(out['graded'])} "
            f"sample {out['sample']} verified {out['verified']} any_sat {out['any_sat']} "
            f"not_verified {out['not_verified'][:10]} cadical_sum {out['cadical_sum']} "
            f"drat_sum {out['drat_sum']} cadical_median {out['cadical_median']} drat_median "
            f"{out['drat_median']} drat_max {out['drat_max']} largest_proof "
            f"{out['largest_proof']} reruns {json.dumps(out['reruns'], sort_keys=True)}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "certify", "grade"], default="check")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "certify":
        certify(args.tools, args.minutes, args.out_dir)
    elif args.part == "grade":
        out = grade(args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = check(args.tools, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'probes'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
