# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job cert2: DRAT proof certificates for every split instance of r3b_t7_B6_o005_c003
(cube_groups/cert2-predictions.md; notes/a77.md).

What came back on 2026-10-22: job cert1 (the pilot, every 20th instance of the class) passed all 10
graded checks, and all 99 sampled instances were UNSAT in a standalone CaDiCaL with every DRAT proof
VERIFIED by drat-trim, in 490 s for the 99 (CaDiCaL 191.55 s, drat-trim 207.06 s in all). Under
cert1-predictions.md's rule the whole class is certified next, in two jobs split by m66's order.

Group a (job cert2a): k = 0 to 980 (981 instances, 17 of the 32 that m88a-v2 left open).
Group b (job cert2b): k = 981 to 1960 (980 instances, the other 15).
Together they are all 1961 split instances of the class, once each; the 99 of cert1's sample are
certified again, and the SHA-256 of each of their CNFs is compared with cert1's (cert1_sha.json).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Everything but the groups is cert1.py's, imported unchanged: the two programs (built by
cert1_tools.py), the controls, the class gate, the instances (m69.py's split, Lemma 93 (b) on the
rank-0 ones) and one instance's certificate (certify_one).

Parts:
    check    cert1's 10 graded checks, then the group: its instances, in range and once each, Lemma
             93 (b) on exactly those of rank 0, the group's re-runs equal to m90's rows, the two
             groups together exactly the class, cert1's hashes 99. Writes cert2_specs.json and
             check.json.
    certify  each instance of the group in m66's order, as cert1 does; the proof is deleted after
             it is checked.
    grade    counts and times; which instances are not VERIFIED; cert1's hashes compared.

Usage: python cert2.py --part check|certify|grade --group a|b [--tools tools] [--minutes 120]
       [--out-dir DIR]
"""
import argparse
import json
import os
import random
import statistics
import tempfile
import time

import cert1 as c1

b, m90 = c1.b, c1.m90
NAME = c1.NAME
GROUPS = {"a": (0, 981), "b": (981, 1961)}
RERUNS_IN_GROUP = {"a": 17, "b": 15}
SPECS_FILE = "cert2_specs.json"
SHA_FILE = "cert1_sha.json"


def ks(group):
    return tuple(range(*GROUPS[group]))


def group_specs(group, reps):
    """m69's split instance at each root of the group, with Lemma 93 (b) when of rank 0 on X_1."""
    return [b.split_spec(NAME, k, reps[k], reps[k]["rank_x1"] == 0) for k in ks(group)]


def cert1_sha():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), SHA_FILE)
    with open(path) as f:
        return {int(k): v for k, v in json.load(f)["sha256"].items()}


def groups_ok():
    """The two groups are the class's 1961 roots, in order, once each."""
    a, bb = GROUPS["a"], GROUPS["b"]
    return (a[0] == 0 and a[1] == bb[0] and bb[1] == m90.NAMED_GATE[NAME]["orbits"] == 1961
            and sum(k in c1.rerun_rows() for k in ks("a")) == RERUNS_IN_GROUP["a"]
            and sum(k in c1.rerun_rows() for k in ks("b")) == RERUNS_IN_GROUP["b"]
            and sorted(cert1_sha()) == list(c1.SAMPLE))


def specs_ok(group, specs):
    rows = c1.rerun_rows()
    by_k = dict(zip(ks(group), specs))
    return (len(specs) == len(ks(group))
            and len({sp["name"] for sp in specs}) == len(specs)
            and all(sp["parent"] == NAME and bool(sp.get("lemma93")) == (sp["rank_x1"] == 0)
                    and sp["name"] == m90.named_name(NAME, k, sp["rank_x1"])
                    for k, sp in by_k.items())
            and all(by_k[k]["m66_index"] == rows[k][3] and by_k[k]["size"] == rows[k][4]
                    and by_k[k]["a1"] == rows[k][5] and by_k[k]["rank_x1"] == rows[k][2]
                    for k in rows if k in by_k))


# ---------- parts ----------

def check(tools, group, out_dir):
    start = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        st = c1.check(tools, tmp)
    graded, probes = dict(st["graded"]), dict(st["probes"])
    _, rr = b.class_reps(NAME, random.Random(90))
    specs = group_specs(group, rr)
    graded["groups"] = groups_ok()
    graded["group"] = specs_ok(group, specs)
    with open(os.path.join(out_dir, SPECS_FILE), "w") as f:
        json.dump(specs, f)
    out = {"group": group, "graded": graded, "probes": probes, "instances": len(specs),
           "ranks": {str(k): sum(sp["rank_x1"] == k for sp in specs) for k in (0, 1, 2)},
           "seconds": round(time.time() - start, 1)}
    with open(os.path.join(out_dir, "check.json"), "w") as f:
        json.dump(out, f, indent=1)
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
                out = c1.certify_one(tools, sp, tmp)
            with open(os.path.join(out_dir, f"cert2_{sp['name']}.json"), "w") as f:
                json.dump(out, f, indent=1)
            counts[out["status"]] = counts.get(out["status"], 0) + 1
            print(f"certify {sp['name']}: {out['status']} cadical "
                  f"{out.get('cadical', {}).get('seconds')} s drat "
                  f"{(out.get('drat') or {}).get('seconds')} s proof {out.get('proof_bytes')} B",
                  flush=True)
    print(f"SUMMARY certify {json.dumps(counts, sort_keys=True)} seconds "
          f"{round(time.time() - start)}", flush=True)


def grade(group, out_dir):
    with open(os.path.join(out_dir, "check.json")) as f:
        graded = json.load(f)["graded"]
    with open(os.path.join(out_dir, SPECS_FILE)) as f:
        specs = json.load(f)
    rows = []
    for sp in specs:
        p = os.path.join(out_dir, f"cert2_{sp['name']}.json")
        rows.append(json.load(open(p)) if os.path.exists(p) else
                    {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "MISSING"})
    done = [r for r in rows if r["status"] == "VERIFIED"]
    cad = [r["cadical"]["seconds"] for r in done]
    drt = [r["drat"]["seconds"] for r in done]
    big = max(done, key=lambda r: r["proof_bytes"], default=None)
    slow = max(done, key=lambda r: r["cadical"]["seconds"] + r["drat"]["seconds"], default=None)
    sha = cert1_sha()
    by_k = {int(r["name"][-4:]): r for r in rows}
    compared = [k for k in sha if k in by_k and "cnf_sha256" in by_k[k]]
    reruns = c1.rerun_rows()
    counts = {}
    for r in rows:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    tj = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools", "tools.json")
    return {"class": NAME, "group": group, "graded": graded, "instances": len(specs),
            "tools": json.load(open(tj)) if os.path.exists(tj) else None,
            "counts": counts, "verified": len(done),
            "not_verified": [r["name"] for r in rows if r["status"] != "VERIFIED"],
            "any_sat": any(r["status"] == "SAT" for r in rows),
            "cadical_sum": round(sum(cad), 2), "drat_sum": round(sum(drt), 2),
            "cadical_median": statistics.median(cad) if cad else None,
            "drat_median": statistics.median(drt) if drt else None,
            "cadical_max": max(cad, default=None), "drat_max": max(drt, default=None),
            "largest_proof": [big["name"], big["proof_bytes"]] if big else None,
            "slowest": ([slow["name"], slow["cadical"]["seconds"], slow["drat"]["seconds"]]
                        if slow else None),
            "sha_compared": len(compared),
            "sha_differ": [by_k[k]["name"] for k in compared
                           if by_k[k]["cnf_sha256"] != sha[k]],
            "reruns": {by_k[k]["name"]: [by_k[k]["status"],
                                         by_k[k].get("cadical", {}).get("seconds"),
                                         (by_k[k].get("drat") or {}).get("seconds")]
                       for k in sorted(reruns) if k in by_k}}


def summary_line(out):
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} graded "
            f"{len(out['graded'])} instances {out['instances']} verified {out['verified']} "
            f"counts {json.dumps(out['counts'], sort_keys=True)} any_sat {out['any_sat']} "
            f"not_verified {out['not_verified'][:10]} cadical_sum {out['cadical_sum']} drat_sum "
            f"{out['drat_sum']} cadical_median {out['cadical_median']} cadical_max "
            f"{out['cadical_max']} drat_max {out['drat_max']} largest_proof "
            f"{out['largest_proof']} slowest {out['slowest']} sha_compared {out['sha_compared']} "
            f"sha_differ {out['sha_differ'][:10]}")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "certify", "grade"], default="check")
    ap.add_argument("--group", choices=sorted(GROUPS), default="a")
    ap.add_argument("--tools", default="tools")
    ap.add_argument("--minutes", type=float, default=120.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "certify":
        certify(args.tools, args.minutes, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
        print(summary_line(out), flush=True)
    else:
        st = check(args.tools, args.group, args.out_dir)
        print(f"check: {json.dumps({k: v for k, v in st.items() if k != 'probes'}, sort_keys=True)}",
              flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)


if __name__ == "__main__":
    main()
