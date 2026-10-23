# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job cert3: DRAT proof certificates for the 45 split instances of (B6) that job m92 re-ran, the
last ones behind Theorem 33 (cube_groups/cert3-predictions.md; notes/a80.md).

What came back on 2026-10-23: m92a and m92b found all 45 instances that m91a and m91b had left open
in o003_c000 and o005_c000 UNSAT in CaDiCaL (through python-sat), in 14.51 to 94.22 s each, so
(B6) is empty and A(7) <= 8 (Theorem 33, computer-assisted). They are among the hardest instances
of the whole chain, and none has a certificate. This job rebuilds each with the very same code,
solves it with a standalone CaDiCaL that writes a DRAT proof, and checks the proof with drat-trim.

Group a (job cert3a): the 25 of r3b_t7_B6_o003_c000 (all of rank 0, with Lemma 93 (b)).
Group b (job cert3b): the 20 of r3b_t7_B6_o005_c000 (18 of rank 0, 2 of rank 1).

A VERIFIED answer certifies that the CNF has no solution. It does not certify the encoding, the
hints, Lemma 93 or Proposition 33, which are hand arguments and code that no human has checked.

Everything but the groups is cert1.py's, imported unchanged: the two programs (built by
cert1_tools.py), the controls, and one instance's certificate (certify_one). The instances, the class
gates and the rows are m92.py's, imported unchanged; m69.py's split_spec builds each instance.

Parts:
    check    cert1's 10 graded checks, then the group: its class against m66's run (m92's gate) and
             its roots recomputed; its instances, once each, equal to m92's rows (name, m66 index,
             orbit size, A_(v_1), rank), Lemma 93 (b) on exactly those of rank 0; the variable,
             clause, hint and unit counts of the first instance of each kind equal to m92's own
             check. Writes cert3_specs.json and check.json.
    certify  each instance of the group in m92's order, as cert1 does; the proof is deleted after
             it is checked.
    grade    counts and times; which instances are not VERIFIED.

Usage: python cert3.py --part check|certify|grade --group a|b [--tools tools] [--minutes 120]
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
import m92

b, m = c1.b, c1.m
GROUPS = {"a": "r3b_t7_B6_o003_c000", "b": "r3b_t7_B6_o005_c000"}
# m92's own check (compete-results/m92a-b6rerun-v1 and m92b-b6rerun-v1, check.json probes,
# 2026-10-23): [vars, clauses, hints, units] of the first rank-0 instance ("l") and the first
# rank-1 instance ("s") of the group, CaDiCaL arm.
M92_PROBES = {"a": {"l": [48587, 286225, 79, 70]},
              "b": {"l": [48587, 286239, 79, 70], "s": [48587, 286218, 79, 49]}}
SPECS_FILE = "cert3_specs.json"


def rows(group):
    """m92's rows of the group: (class, k, rank on X_1, m66 index, orbit size, A_(v_1))."""
    return m92.named_rows(group)


def group_specs(group, reps):
    """m69's split instance at each of the group's roots, with Lemma 93 (b) when of rank 0."""
    return [b.split_spec(name, k, reps[k], rk == 0) for name, k, rk, _, _, _ in rows(group)]


def groups_ok():
    """The two groups are m92's two classes, with its 25 and 20 rows."""
    return (sorted(GROUPS.values()) == sorted(m92.NAMED_CLASSES)
            and all({r[0] for r in rows(g)} == {GROUPS[g]} for g in GROUPS)
            and [len(rows(g)) for g in ("a", "b")] == [m92.NAMED_COUNT["a"], m92.NAMED_COUNT["b"]]
            == [25, 20] and m92.lists_ok())


def specs_ok(group, specs):
    rs = rows(group)
    return (len(specs) == len(rs) == m92.NAMED_COUNT[group]
            and len({sp["name"] for sp in specs}) == len(specs)
            and all(sp["parent"] == name == GROUPS[group]
                    and sp["name"] == m92.named_name(name, k, rk)
                    and sp["m66_index"] == index and sp["size"] == size and sp["a1"] == a1
                    and sp["rank_x1"] == rk and bool(sp.get("lemma93")) == (rk == 0)
                    for sp, (name, k, rk, index, size, a1) in zip(specs, rs)))


def probe(sp):
    c, _, h, u = m.build(dict(sp), "cadical")
    return [c.nv, len(c.clauses), h, u], m.units_consistent(c)


# ---------- parts ----------

def check(tools, group, out_dir):
    start = time.time()
    with tempfile.TemporaryDirectory() as tmp:
        st = c1.check(tools, tmp)
    graded, probes = dict(st["graded"]), dict(st["probes"])
    name = GROUPS[group]
    gate = m92.NAMED_GATE[name]
    r, rr = b.class_reps(name, random.Random(92))
    graded["class"] = m92.class_ok(r, gate)
    graded["class_reps"] = m92.reps_ok(name, rr, gate)
    graded["groups"] = groups_ok()
    specs = group_specs(group, rr)
    graded["group"] = specs_ok(group, specs)
    for tag, want in M92_PROBES[group].items():
        sp = next(x for x in specs if bool(x.get("lemma93")) == (tag == "l"))
        got, consistent = probe(sp)
        probes["m92_" + tag] = [sp["name"]] + got
        graded["m92_probe_" + tag] = got == want and consistent
    with open(os.path.join(out_dir, SPECS_FILE), "w") as f:
        json.dump(specs, f)
    out = {"group": group, "class": name, "graded": graded, "probes": probes,
           "instances": len(specs),
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
            with open(os.path.join(out_dir, f"cert3_{sp['name']}.json"), "w") as f:
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
    rs = []
    for sp in specs:
        p = os.path.join(out_dir, f"cert3_{sp['name']}.json")
        rs.append(json.load(open(p)) if os.path.exists(p) else
                  {"name": sp["name"], "rank_x1": sp["rank_x1"], "status": "MISSING"})
    done = [r for r in rs if r["status"] == "VERIFIED"]
    cad = [r["cadical"]["seconds"] for r in done]
    drt = [r["drat"]["seconds"] for r in done]
    big = max(done, key=lambda r: r["proof_bytes"], default=None)
    slow = max(done, key=lambda r: r["cadical"]["seconds"] + r["drat"]["seconds"], default=None)
    counts = {}
    for r in rs:
        counts[r["status"]] = counts.get(r["status"], 0) + 1
    tj = os.path.join(os.path.dirname(os.path.abspath(__file__)), "tools", "tools.json")
    return {"class": GROUPS[group], "group": group, "graded": graded, "instances": len(specs),
            "tools": json.load(open(tj)) if os.path.exists(tj) else None,
            "counts": counts, "verified": len(done),
            "not_verified": [r["name"] for r in rs if r["status"] != "VERIFIED"],
            "any_sat": any(r["status"] == "SAT" for r in rs),
            "cadical_sum": round(sum(cad), 2), "drat_sum": round(sum(drt), 2),
            "cadical_median": statistics.median(cad) if cad else None,
            "drat_median": statistics.median(drt) if drt else None,
            "cadical_max": max(cad, default=None), "drat_max": max(drt, default=None),
            "largest_proof": [big["name"], big["proof_bytes"]] if big else None,
            "slowest": ([slow["name"], slow["cadical"]["seconds"], slow["drat"]["seconds"]]
                        if slow else None),
            "rows": {r["name"]: [r["status"], r.get("cadical", {}).get("seconds"),
                                 (r.get("drat") or {}).get("seconds"), r.get("proof_bytes"),
                                 r.get("cnf_sha256")]
                     for r in rs}}


def summary_line(out):
    return (f"SUMMARY grade group {out['group']} all_match {all(out['graded'].values())} graded "
            f"{len(out['graded'])} instances {out['instances']} verified {out['verified']} "
            f"counts {json.dumps(out['counts'], sort_keys=True)} any_sat {out['any_sat']} "
            f"not_verified {out['not_verified'][:10]} cadical_sum {out['cadical_sum']} drat_sum "
            f"{out['drat_sum']} cadical_median {out['cadical_median']} cadical_max "
            f"{out['cadical_max']} drat_max {out['drat_max']} largest_proof "
            f"{out['largest_proof']} slowest {out['slowest']}")


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
