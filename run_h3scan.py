# SPDX-License-Identifier: Apache-2.0
"""run_h3scan.py - driver of the pre-registered job h3scan (notes/prereg-h3scan.md).

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Standard library only (needs gcc for h3scan.c).

Compiles h3scan.c, runs the three exhaustive families (cyclic degree <= 3, S_3-equivariant,
all quadratic maps with the linear part reduced to class representatives), re-checks every
reported map exactly in Python (h3scan.py, integer arithmetic) and writes one JSON file with
the pre-registered grade: RECORD, NO_GAIN or INCOMPLETE.

Usage: python run_h3scan.py --out /out/h3scan.json [--workers 2] [--budget-minutes 150]
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

import h3scan

HERE = os.path.dirname(os.path.abspath(__file__))
EXPECTED = {"quadratic": 3 ** 18, "s3": 3 ** 18, "cyclic": 3 ** 16}


def ensure_gcc():
    if shutil.which("gcc"):
        return
    subprocess.run("apt-get update -qq && apt-get install -y -qq gcc", shell=True, check=False)
    if not shutil.which("gcc"):
        raise SystemExit("gcc not available")


def compile_c(outdir):
    exe = os.path.join(outdir, "h3scan_bin.exe" if os.name == "nt" else "h3scan_bin")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "h3scan.c"), "-lm"], check=True)
    return exe


def parse_output(text):
    res = {"above": [], "near": [], "top": [], "total": None, "counts": None}
    for line in text.splitlines():
        p = line.split()
        if not p:
            continue
        if p[0] in ("ABOVE", "NEAR"):
            res[p[0].lower()].append({"enc": [int(v) for v in p[2:-1]], "S_c": float(p[-1])})
        elif p[0] == "TOP":
            res["top"].append({"S_c": float(p[2]), "count": int(p[3]),
                               "enc": [int(v) for v in p[4:]]})
        elif p[0] == "TOTAL":
            res["total"] = int(p[2])
        elif p[0] == "COUNTS":
            res["counts"] = {"above": int(p[2]), "equal": int(p[3]), "near": int(p[4])}
    return res


def build_map(family, L, enc):
    if family == "quadratic":
        return h3scan.quad_map(L, enc[0], enc[1], enc[2])
    if family == "s3":
        return h3scan.s3_map(enc[0])
    return h3scan.cyc_map(enc[0])


def recheck(family, L, item):
    P = build_map(family, L, item["enc"])
    S = h3scan.S_float(P)
    item["S_python"] = S
    item["agree"] = abs(S - item["S_c"]) < 1e-6
    item["vs_162_exact"] = h3scan.compare_162(P)
    item["base"] = h3scan.base_from_S(S)
    item["map"] = [list(v) for v in P]
    return item


def run_guarded(exe, args, deadline):
    now = time.time()
    if now > deadline - 30:
        return {"status": "skipped_budget"}
    t0 = time.time()
    try:
        r = subprocess.run([exe] + [str(a) for a in args], capture_output=True, text=True,
                           timeout=max(30.0, deadline - now))
    except subprocess.TimeoutExpired:
        return {"status": "timeout", "seconds": time.time() - t0}
    return {"status": "ok" if r.returncode == 0 else "error", "returncode": r.returncode,
            "stdout": r.stdout, "stderr": r.stderr[-2000:], "seconds": time.time() - t0}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--budget-minutes", type=float, default=150.0)
    args = ap.parse_args()
    start = time.time()
    deadline = start + 60.0 * args.budget_minutes
    outdir = os.path.dirname(os.path.abspath(args.out))
    os.makedirs(outdir, exist_ok=True)

    ensure_gcc()
    gcc_version = subprocess.run(["gcc", "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    exe = compile_c(outdir)

    reps = h3scan.conj_shift_reps()
    assert sum(n for _, n in reps) == 3 ** 9
    print("linear-part classes:", len(reps), flush=True)

    tasks = [("cyclic", None, ["cyc"]), ("s3", None, ["s3"])]
    for L, size in reps:
        tasks.append(("quadratic", L, ["quad"] + h3scan.flat(L)))

    with ThreadPoolExecutor(max_workers=max(1, args.workers)) as ex:
        futs = [(fam, L, a, ex.submit(run_guarded, exe, a, deadline)) for fam, L, a in tasks]
        runs = []
        for fam, L, a, fu in futs:
            r = fu.result()
            entry = {"family": fam, "args": a, "status": r["status"],
                     "seconds": round(r.get("seconds", 0.0), 1)}
            if L is not None:
                entry["L"] = [list(row) for row in L]
                entry["class_size"] = dict((k, n) for k, n in reps)[L]
            if r["status"] == "ok":
                res = parse_output(r["stdout"])
                entry["total"] = res["total"]
                entry["counts"] = res["counts"]
                entry["complete"] = (res["total"] == EXPECTED[fam])
                entry["above"] = [recheck(fam, L, it) for it in res["above"]]
                entry["near"] = [recheck(fam, L, it) for it in res["near"]]
                entry["top"] = [recheck(fam, L, it) for it in res["top"]]
            else:
                entry["complete"] = False
                entry["stderr"] = r.get("stderr", "")
            print(fam, a, entry["status"], entry.get("counts"), entry["seconds"], "s", flush=True)
            runs.append(entry)

    families = {}
    any_record = False
    all_agree = True
    for fam in ("cyclic", "s3", "quadratic"):
        rs = [r for r in runs if r["family"] == fam]
        tops = [it for r in rs for it in r.get("top", [])]
        checked = [it for r in rs for key in ("above", "near", "top") for it in r.get(key, [])]
        rec = [it for it in checked if it["vs_162_exact"] > 0]
        any_record = any_record or bool(rec)
        all_agree = all_agree and all(it["agree"] for it in checked)
        best = max(tops, key=lambda it: it["S_python"]) if tops else None
        distinct = sorted({round(it["S_python"], 9) for it in tops}, reverse=True)
        families[fam] = {
            "runs": len(rs),
            "complete": bool(rs) and all(r.get("complete") for r in rs),
            "maps_scanned": sum(r.get("total") or 0 for r in rs),
            "above_162": sum((r.get("counts") or {}).get("above", 0) for r in rs),
            "equal_162": sum((r.get("counts") or {}).get("equal", 0) for r in rs),
            "near_162_not_equal": sum((r.get("counts") or {}).get("near", 0) for r in rs),
            "max_S": best["S_python"] if best else None,
            "max_S_base": best["base"] if best else None,
            "max_S_example": best["map"] if best else None,
            "top_values": distinct[:8],
            "record_examples": rec[:5],
        }

    if any_record:
        grade = "RECORD"
    elif all(f["complete"] for f in families.values()):
        grade = "NO_GAIN"
    else:
        grade = "INCOMPLETE"

    out = {
        "job": "h3scan",
        "prereg": "notes/prereg-h3scan.md",
        "made_by": "MV2 of Munim, Inc.; made with AI agents working in MV2's name",
        "gcc": gcc_version,
        "seconds_total": round(time.time() - start, 1),
        "linear_classes": len(reps),
        "grade": grade,
        "c_and_python_agree": all_agree,
        "families": families,
        "runs": runs,
    }
    with open(args.out, "w") as fh:
        json.dump(out, fh, indent=1)
    print("GRADE", grade, flush=True)


if __name__ == "__main__":
    sys.exit(main())
