# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m128: reconcile the d = 1 certificate tally of (B7)_8 against the full case list
(notes/a108.md to a121.md; cube_groups/m128-predictions.md).

The notes keep a running count of d = 1 cases with a drat-trim-checked certificate, now 3,846 of
3,876 after m127. Before any claim about the class, this job recounts from the published files
alone: every `*_grade.json` under cube_groups/results/ in the repository, read as published, and
m113's list of the 3,876 d = 1 cases (m113.d1_cases, built from m110.sweep_cases).

Parts:

    list      the repository tree (GitHub API); every grade file under cube_groups/results/
    fetch     download them all, plus the eight m127 grade files (waiting for them if needed)
    count     per d = 1 case: every status any grade file gives it, and in which file; VERIFIED
              means a checked certificate; the cases with none; the m110 UNSAT answers
              (m113.decided over m111.m110_parts)
    grade     the graded checks of m128-predictions.md

Usage: python m128.py --part list|fetch|count|grade [--out-dir D]
       (m113.py and its imports in the working directory, as for m127)
"""
import argparse
import json
import os
import time
import urllib.request

REPO_API = ("https://api.github.com/repos/munimtechnologies/kakeya-small-fields/git/trees/main"
            "?recursive=1")
RAW = "https://raw.githubusercontent.com/munimtechnologies/kakeya-small-fields/main/"
RESULTS = "cube_groups/results/"
GRADES_DIR = "grades"
M127 = [f"{RESULTS}m127{s}/m127{s}_grade.json" for s in "abcdefgh"]
N_D1 = 3876
TALLY_A121 = 3846


def save(out_dir, name, obj):
    with open(os.path.join(out_dir, name), "w") as f:
        json.dump(obj, f, indent=1)


def load(out_dir, name):
    path = os.path.join(out_dir, name)
    if not os.path.exists(path):
        return None
    with open(path) as f:
        return json.load(f)


def get(url, tries=5):
    for k in range(tries):
        try:
            req = urllib.request.Request(url, headers={"User-Agent": "mv2-m128"})
            with urllib.request.urlopen(req, timeout=60) as r:
                return r.read()
        except Exception as e:  # retried, then raised
            print(f"{url}: attempt {k + 1} failed ({e})", flush=True)
            time.sleep(20)
    raise RuntimeError(f"could not download {url}")


def local_name(path):
    return path[len(RESULTS):].replace("/", "__")


# ---------- reading grade files ----------

def statuses(g):
    """{instance: status} from one grade file: `rows` as a dict of lists whose first item is the
    status (m113.grade_rows), or a list of dicts with `instance` and `cert`."""
    out = {}
    rows = g.get("rows") if isinstance(g, dict) else None
    if isinstance(rows, dict):
        for x, row in rows.items():
            if isinstance(row, (list, tuple)) and row and isinstance(row[0], str):
                out[x] = row[0]
            elif isinstance(row, dict) and isinstance(row.get("cert"), str):
                out[x] = row["cert"]
    elif isinstance(rows, list):
        for r in rows:
            if isinstance(r, dict) and isinstance(r.get("instance"), str) and \
                    isinstance(r.get("cert"), str):
                out[r["instance"]] = r["cert"]
    return out


def reconcile(d1, files):
    """From {file: {instance: status}} and the d = 1 names: per case the statuses seen, the
    VERIFIED set, the cases with none, and d = 1 cases reported SAT or NOT_VERIFIED anywhere."""
    seen = {}
    for fname, st in files.items():
        for x, s in st.items():
            if x in d1:
                seen.setdefault(x, []).append([s, fname])
    verified = sorted(x for x, v in seen.items() if any(s == "VERIFIED" for s, _ in v))
    vset = set(verified)
    missing = sorted(x for x in d1 if x not in vset)
    bad = sorted(x for x, v in seen.items()
                 if any(s in ("SAT", "NOT_VERIFIED") for s, _ in v))
    by_file = {}
    for x in verified:
        first = sorted(f for s, f in seen[x] if s == "VERIFIED")[0]
        by_file[first] = by_file.get(first, 0) + 1
    return {"verified": verified, "missing": missing, "bad": bad, "seen": seen,
            "first_verified_by_file": by_file}


# ---------- the parts ----------

def part_list(args):
    tree = json.loads(get(REPO_API))
    paths = sorted(t["path"] for t in tree.get("tree", [])
                   if t.get("type") == "blob" and t["path"].startswith(RESULTS)
                   and t["path"].endswith("_grade.json"))
    save(args.out_dir, "m128_list.json", {"truncated": tree.get("truncated"), "paths": paths})
    print(f"SUMMARY list grade_files {len(paths)} truncated {tree.get('truncated')}", flush=True)


def part_fetch(args):
    info = load(args.out_dir, "m128_list.json") or {"paths": []}
    paths = sorted(set(info["paths"]) | set(M127))
    os.makedirs(GRADES_DIR, exist_ok=True)
    got, failed = [], []
    for p in paths:
        wait = 40 if p in M127 and p not in info["paths"] else 1
        for k in range(wait):
            try:
                data = get(RAW + p, tries=2)
                with open(os.path.join(GRADES_DIR, local_name(p)), "wb") as f:
                    f.write(data)
                got.append(p)
                break
            except RuntimeError:
                if k + 1 < wait:
                    time.sleep(60)
        else:
            failed.append(p)
    save(args.out_dir, "m128_fetch.json", {"got": got, "failed": failed})
    print(f"SUMMARY fetch got {len(got)} failed {len(failed)} {failed[:10]}", flush=True)


def part_count(args):
    import m111
    import m113
    d1 = set(m113.d1_cases())
    files, unreadable = {}, []
    for fname in sorted(os.listdir(GRADES_DIR)):
        try:
            with open(os.path.join(GRADES_DIR, fname)) as f:
                files[fname] = statuses(json.load(f))
        except (OSError, ValueError) as e:
            unreadable.append([fname, str(e)])
    rec = reconcile(d1, files)
    parts = m111.m110_parts("abcdefghij")
    decided = {x: m for x, m in m113.decided(parts or {})}
    missing_info = {x: {"m110_unsat_mode": decided.get(x),
                        "statuses": rec["seen"].get(x, [])} for x in rec["missing"]}
    labels = {}
    for x in rec["missing"]:
        labels[x[20:]] = labels.get(x[20:], 0) + 1
    out = {"n_d1": len(d1), "n_files": len(files), "files_with_d1_rows":
           sorted(f for f, st in files.items() if any(x in d1 for x in st)),
           "unreadable": unreadable, "n_verified": len(rec["verified"]),
           "n_missing": len(rec["missing"]), "bad": rec["bad"], "missing": missing_info,
           "missing_by_label": labels, "first_verified_by_file": rec["first_verified_by_file"],
           "m110_decided": len(decided),
           "missing_with_m110_unsat": sorted(x for x in rec["missing"] if x in decided)}
    save(args.out_dir, "m128_count.json", out)
    save(args.out_dir, "m128_verified_names.json", rec["verified"])
    print(f"SUMMARY count d1 {out['n_d1']} files {out['n_files']} verified {out['n_verified']} "
          f"missing {out['n_missing']} bad {len(out['bad'])} missing_with_m110_unsat "
          f"{len(out['missing_with_m110_unsat'])} by_label {json.dumps(labels, sort_keys=True)}",
          flush=True)


def grade(out_dir):
    c = load(out_dir, "m128_count.json") or {}
    lst = load(out_dir, "m128_list.json") or {}
    fe = load(out_dir, "m128_fetch.json") or {}
    g = {
        "listed": bool(lst.get("paths")) and not lst.get("truncated"),
        "fetched_all": bool(fe.get("got")) and not fe.get("failed"),
        "m127_present": all(p in (fe.get("got") or []) for p in M127),
        "d1_3876": c.get("n_d1") == N_D1,
        "no_unreadable": c.get("unreadable") == [],
        "tally_matches_a121": c.get("n_verified") == TALLY_A121,
        "missing_30": c.get("n_missing") == N_D1 - TALLY_A121,
        "no_sat_or_not_verified": c.get("bad") == [],
        "missing_have_no_m110_unsat": c.get("missing_with_m110_unsat") == [],
    }
    return {"graded": g, "n_verified": c.get("n_verified"), "n_missing": c.get("n_missing"),
            "missing_by_label": c.get("missing_by_label"), "n_files": c.get("n_files")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["list", "fetch", "count", "grade"], default="list")
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "grade":
        out = grade(args.out_dir)
        save(args.out_dir, "m128_grade.json", out)
        bad = sorted(k for k, v in out["graded"].items() if not v)
        print(f"SUMMARY grade all_match {not bad} failed {bad} verified {out['n_verified']} "
              f"missing {out['n_missing']} {json.dumps(out['missing_by_label'], sort_keys=True)}",
              flush=True)
        return
    part = {"list": part_list, "fetch": part_fetch, "count": part_count}[args.part]
    try:
        part(args)
    except Exception as e:  # recorded; the later parts still run
        save(args.out_dir, f"m128_{args.part}_error.json", {"error": repr(e)})
        print(f"SUMMARY {args.part} error {e!r}", flush=True)


if __name__ == "__main__":
    main()
