# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Runs the pre-registered f3cert experiment (f3cert/PREREG.md) with the pure-stdlib LP of
f3cert/dlp.py instead of scipy, so it fits a plain Python 3.11 test run.

Same configurations, rows, variants, alarms and outcome codes as PREREG.md; two differences in
execution only: (1) the LP is the cutting-plane dual simplex of dlp.py (every reported bound is
recomputed exactly from its dual vector, so it is sound whether or not the LP reached its
optimum; "status" says whether it did); (2) each variant has a time budget.  One extra pool,
"cross", is added after the pre-registered ones: for every certificate row (K, i, j), the other
five pairs of the four F_3-lines i, j, i + j, i - j of span(i, j) (over Z there would be infinitely
many such lines; over F_3 there are exactly four).

Output (out_dir): results.json, SUMMARY.md, best_cert.json (the best symmetric variant's exact
certificate), control_cert.json, log.txt."""
import json
import math
import os
import random
import time
from fractions import Fraction

try:
    from . import f3cert as F
    from . import dlp
except ImportError:  # pragma: no cover
    import f3cert as F
    import dlp

OWN_GAIN_MARGIN = Fraction(1, 10 ** 6)


def fr(q):
    q = Fraction(q)
    return "%d/%d" % (q.numerator, q.denominator)


# ------------------------------------------------------------------ rows -> LP columns

class Model:
    """Maps entropy classes to LP columns: the class of d0 is the constant 1 (normalisation
    h(d0) = 1), a class containing the zero space is the constant 0, the classes of x0, y0, s0
    share the column "W" in symmetric variants (rotation trick, PREREG.md)."""

    def __init__(self, reg, sym_cids, uniform):
        self.reg = reg
        x, y, s, d, xy = F.vertex0(reg)
        self.droot = reg.find(d)
        self.symroots = set(reg.find(c) for c in sym_cids)
        self.uniform = uniform
        self.nverts = reg.cfg.nv()
        self.problems = []
        if self.droot in self.symroots:
            self.problems.append("d0 shares a class with x0, y0 or s0")

    def key(self, cid):
        r = self.reg.find(cid)
        if r == self.droot:
            return None, 1
        if self.reg.ub[r] == 0:
            return None, 0
        if r in self.symroots:
            return "W", None
        return r, None

    def compile(self, terms):
        co, const = {}, 0
        for cid, a in terms:
            k, v = self.key(cid)
            if k is None:
                const += a * v
            else:
                co[k] = co.get(k, 0) + a
        return {k: a for k, a in co.items() if a != 0}, const

    def ub(self, k):
        if k == "W":
            return min(self.reg.ub[r] for r in self.symroots)
        return self.reg.ub[k]

    def hi(self, k):
        h = self.nverts
        if self.uniform:
            h = min(h, self.ub(k))
        return h

    def gens(self, k):
        if k == "W":
            r = min(self.symroots, key=lambda q: self.reg.ub[q])
        else:
            r = k
        m = self.reg.cfg.nsym
        return [F.to_digits(v, m) for v in self.reg.ubspan[r]]

    def name(self, k):
        return "W" if k == "W" else "c%d" % k


def spec_json(spec, m):
    def vd(v):
        return F.to_digits(v, m)
    t = spec[0]
    if t in ("sub", "meet"):
        return {"type": t, "K": [vd(v) for v in spec[1]], "i": vd(spec[2]), "j": vd(spec[3])}
    if t == "mono":
        return {"type": t, "K": [vd(v) for v in spec[1]], "i": vd(spec[2]), "j": vd(spec[3]),
                "which": spec[4]}
    if t == "ci":
        return {"type": "ci", "step": spec[1], "sign": spec[2]}
    if t == "unif":
        return {"type": "unif", "key": spec[1], "bound": spec[2]}
    return {"type": str(t)}


def run_variant(name, reg, cost_cids, sym, uniform, init_terms, pool_terms, eq_terms,
                deadline, log):
    t0 = time.time()
    model = Model(reg, sym, uniform)
    rows, specs, seen = [], [], {}
    nconst_bad = 0

    def add(terms, spec, is_init):
        nonlocal nconst_bad
        co, c = model.compile(terms)
        if not co:
            if c < 0:
                nconst_bad += 1
            return None
        sig = (tuple(sorted(co.items(), key=lambda kv: str(kv[0]))), c)
        if sig in seen:
            return seen[sig] if is_init else None
        seen[sig] = len(rows)
        rows.append((co, c))
        specs.append(spec)
        return len(rows) - 1

    init = []
    for terms, spec in eq_terms:
        neg = [(cid, -a) for cid, a in terms]
        for tt, sg in ((terms, 1), (neg, -1)):
            idx = add(tt, ("ci", spec[1], sg), True)
            if idx is not None:
                init.append(idx)
    for terms, spec in init_terms:
        idx = add(terms, spec, True)
        if idx is not None:
            init.append(idx)
    for terms, spec in pool_terms:
        add(terms, spec, False)
    if uniform:
        keys = set()
        for co, _c in rows:
            keys.update(co)
        for k in sorted(keys, key=str):
            h = model.hi(k)
            if h < model.nverts:
                rows.append(({k: -1}, h))
                specs.append(("unif", model.name(k), h))
    cost = {}
    for cid, a in cost_cids.items():
        k, v = model.key(cid)
        if k is None:
            model.problems.append("objective term is a constant class")
            continue
        cost[k] = cost.get(k, Fraction(0)) + Fraction(a)
    res = dlp.solve(cost, rows, sorted(set(init)), deadline, log=log)
    val, used, boxused = dlp.exact_bound(cost, rows, res["duals"], lambda k: (0, model.hi(k)))
    info = {"status": res["status"], "value_float": res["z"], "lb_exact": fr(val),
            "lb": float(val), "base": 3.0 ** float(val), "pivots": res["pivots"],
            "rows_in_lp": res["rows_in_lp"], "pool_rows": len(rows), "cols": res["cols"],
            "rounds": res["rounds"], "rows_used": len(used), "box_used": len(boxused),
            "seconds": round(time.time() - t0, 1), "const_violations": nconst_bad,
            "problems": model.problems, "uniform": uniform, "symmetric": bool(sym)}
    m = reg.cfg.nsym
    keys_needed = set(cost)
    for idx, _q in used:
        keys_needed.update(rows[idx][0])
    cert = {"variant": name, "lb": fr(val), "nverts": model.nverts, "uniform": uniform,
            "objective": {model.name(k): fr(a) for k, a in cost.items()},
            "rows": [{"spec": spec_json(specs[idx], m), "mult": fr(q),
                      "coeffs": {model.name(k): a for k, a in rows[idx][0].items()},
                      "const": rows[idx][1]} for idx, q in used],
            "box": {model.name(k): [0, model.hi(k)] for k in keys_needed},
            "keys": {model.name(k): {"gens": model.gens(k), "dim_bound": model.ub(k)}
                     for k in keys_needed}}
    log("%s: %s" % (name, json.dumps(info)))
    return info, val, cert


# ------------------------------------------------------------------ the experiment

def own_replay(reg, cert):
    cfg = reg.cfg
    terms, unknown, errors = [], 0, []
    for n, row in enumerate(cert.get("rows", [])):
        m = Fraction(row["mult"])
        try:
            if row["type"] == "sub":
                K = [F.parse_form(cfg, f) for f in row["K"]]
                t, _ = F.sub_row(reg, K, F.parse_form(cfg, row["i"]), F.parse_form(cfg, row["j"]),
                                 False)
            elif row["type"] == "ci":
                s = int(row["step"])
                if not 0 <= s < len(cfg.steps):
                    raise IndexError("ci step %d of %d" % (s, len(cfg.steps)))
                t, _ = F.ci_row(reg, s)
            else:
                unknown += 1
                continue
        except Exception as exc:  # report, never hide
            unknown += 1
            errors.append("row %d: %r" % (n, exc))
            continue
        for cid, a in t:
            terms.append((cid, m * a))
    x, y, s, d, xy = F.vertex0(reg)
    lam = cert.get("lambda", {})
    for cid, key in ((x, "1,0"), (y, "0,1"), (s, "1,1")):
        terms.append((cid, -Fraction(lam.get(key, 0))))
    terms.append((xy, Fraction(1)))
    res = {}
    for cid, a in terms:
        r = reg.find(cid)
        if reg.ub[r] == 0:          # the zero space: h = 0, so its coefficient is irrelevant
            continue
        res[r] = res.get(r, Fraction(0)) + a
    bad = [fr(v) for v in res.values() if v != 0]
    return {"replay_nonzero_classes": len(bad), "replay_unknown_rows": unknown,
            "replay_errors": errors[:10], "replay_residual_sample": sorted(bad)[:10]}


def cert_sub_rows(cfg, cert):
    out = []
    for row in cert.get("rows", []):
        if row.get("type") != "sub":
            continue
        try:
            K = [F.parse_form(cfg, f) for f in row["K"]]
            out.append((K, F.parse_form(cfg, row["i"]), F.parse_form(cfg, row["j"])))
        except Exception:
            continue
    return out


def cross_terms(reg, subs, deadline=None):
    out = []
    for K, i, j in subs:
        if deadline is not None and time.time() > deadline:
            break
        L = [i, j, F.vadd(i, j), F.vsub(i, j)]
        for a in range(4):
            for b in range(a + 1, 4):
                if (a, b) == (0, 1) or L[a] == F.ZERO or L[b] == F.ZERO:
                    continue
                out.append(F.sub_row(reg, K, L[a], L[b], True))
    return out


def pair_terms(reg, deadline, rng):
    L = F.line_readings(reg.cfg, reg)
    pairs = [(a, b) for a in range(len(L)) for b in range(a + 1, len(L))]
    rng.shuffle(pairs)
    out, done = [], 0
    for a, b in pairs:
        if time.time() > deadline:
            break
        f, g = L[a], L[b]
        out.append(F.sub_row(reg, [], f, g, True))
        for l in (F.vadd(f, g), F.vsub(f, g)):
            for h in (f, g):
                out.append(F.sub_row(reg, [], h, l, True))
        done += 1
    return out, done, len(pairs)


PLANS = {
    # name -> list of (variant, objective, symmetric, uniform, pool names)
    "five": [("cert-lambda-plain", "lambda", False, False, []),
             ("cert-sym-plain", "w", True, False, []),
             ("cert-sym-meet", "w", True, False, ["meet", "mono", "base"]),
             ("cert-sym-meet-unif", "w", True, True, ["meet", "mono", "base"]),
             ("cross-sym-meet-unif", "w", True, True, ["meet", "mono", "base", "cross"])],
    "aug": [("aug-sym-meet", "w", True, False, ["meet", "mono", "base", "cross", "pairs", "nbr"]),
            ("aug-sym-meet-unif", "w", True, True,
             ["meet", "mono", "base", "cross", "pairs", "nbr"])],
    "std": [("cert-lambda-plain", "lambda", False, False, []),
            ("cert-sym-plain", "w", True, False, []),
            ("cert-sym-meet-unif", "w", True, True, ["meet", "mono", "base"]),
            ("cross-sym-meet-unif", "w", True, True, ["meet", "mono", "base", "cross"])],
}


def run(plan, cert, out_dir, budget, log=None, cfg_name="", sha="", seed=20261128):
    """Run one plan on one certificate; write results.json, SUMMARY.md, best_cert.json and
    control_cert.json into out_dir.  Returns the results dict."""
    os.makedirs(out_dir, exist_ok=True)
    t0 = time.time()
    end = t0 + budget
    logf = open(os.path.join(out_dir, "log.txt"), "a")

    def say(msg):
        line = "[%7.1fs] %s" % (time.time() - t0, msg)
        logf.write(line + "\n")
        logf.flush()
        if log:
            log(line)

    rng = random.Random(seed)
    cfg = F.build_config(cert["steps"])
    reg = F.Registry(cfg)
    rep = {"plan": plan, "config": cfg_name, "sha256": sha, "vertices": cfg.nv(),
           "symbols": cfg.nsym, "steps": len(cfg.steps), "claimed_C": cert.get("claimed_C"),
           "complete": False, "variants": {}}
    if cert.get("eqlaw"):
        rep["eqlaw_applied"], rep["eqlaw_skipped"] = F.apply_eqlaw(reg, cert)
    if cert.get("rows"):
        rep.update(own_replay(reg, cert))
        types = {}
        for row in cert["rows"]:
            types[str(row.get("type"))] = types.get(str(row.get("type")), 0) + 1
        rep["cert_row_types"] = types
        rep["cert_ci_steps"] = [row.get("step") for row in cert["rows"] if row.get("type") == "ci"]
        rep["cert_lambda"] = cert.get("lambda")
    say("built %s: %d vertices, %d symbols, replay %s" % (
        cfg_name, cfg.nv(), cfg.nsym, rep.get("replay_nonzero_classes")))
    x, y, s, d, xy = F.vertex0(reg)
    subs = cert_sub_rows(cfg, cert)
    pools = {"plain": [F.sub_row(reg, K, i, j, False) for K, i, j in subs],
             "meet": [F.sub_row(reg, K, i, j, True) for K, i, j in subs],
             "mono": [r for K, i, j in subs for r in F.mono_rows(reg, K, i, j)],
             "base": [F.sub_row(reg, [], cfg.X[0], cfg.Y[0], True)]}
    steps = PLANS[plan]
    need = set(p for st in steps for p in st[4])
    if "cross" in need:
        pools["cross"] = cross_terms(reg, subs, t0 + 0.3 * budget)
    if "pairs" in need:
        pools["pairs"], done, tot = pair_terms(reg, t0 + 0.35 * budget, rng)
        rep["pair_lines_done"], rep["pair_lines_total"] = done, tot
    if "nbr" in need and cert.get("rows") and time.time() < t0 + 0.45 * budget:
        small = cfg.nv() <= 40
        pools["nbr"] = F.aug_neighbours(reg, cert, per_pair=30 if small else 12,
                                        per_add=10 if small else 6, rng=rng)
    ci = [F.ci_row(reg, k) for k in range(len(cfg.steps))]
    rep["pool_sizes"] = {k: len(v) for k, v in pools.items()}
    rep["classes"] = len(reg.parent)
    rep["build_seconds"] = round(time.time() - t0, 1)
    say("pools %s, %d classes" % (json.dumps(rep["pool_sizes"]), len(reg.parent)))
    lam = cert.get("lambda") or {}
    best = None
    control = None
    for n, (vname, obj, sym, uni, pnames) in enumerate(steps):
        if obj == "lambda" and not lam:
            continue
        if not pools["plain"] and not any(pools.get(p) for p in pnames):
            continue
        left = len(steps) - n
        dl = time.time() + max(5.0, (end - time.time()) / left)
        if obj == "lambda":
            cost = {}
            for cid, key in ((x, "1,0"), (y, "0,1"), (s, "1,1")):
                cost[cid] = cost.get(cid, Fraction(0)) + Fraction(lam.get(key, 0))
        else:
            cost = {x: Fraction(1)}
        pool = [r for p in pnames for r in pools.get(p, [])]
        try:
            info, val, c = run_variant(vname, reg, cost, [x, y, s] if sym else [], uni,
                                       pools["plain"], pool, ci, dl, say)
        except Exception as exc:  # report, never hide
            import traceback
            info, val, c = {"error": repr(exc), "trace": traceback.format_exc()[-1500:]}, None, None
            say("%s failed: %r" % (vname, exc))
        rep["variants"][vname] = info
        if c is not None:
            if sym and (best is None or val > best[0]):
                best = (val, vname, c)
            if obj == "lambda":
                control = c
        _write(out_dir, rep)
    rep["verdict"] = verdict(rep)
    if best is not None:
        rep["best_variant"] = best[1]
        rep["best_lb_exact"] = fr(best[0])
        rep["best_lb"] = float(best[0])
        rep["best_base"] = 3.0 ** float(best[0])
    rep["complete"] = True
    rep["seconds"] = round(time.time() - t0, 1)
    _write(out_dir, rep)
    for fname, c in (("best_cert.json", best[2] if best else None), ("control_cert.json", control)):
        with open(os.path.join(out_dir, fname), "w") as fh:
            json.dump(c if c is not None else {"none": True}, fh)
    with open(os.path.join(out_dir, "SUMMARY.md"), "w") as fh:
        fh.write(summary_md(rep))
    say("VERDICT %s" % rep["verdict"])
    logf.close()
    return rep


def verdict(rep):
    v = rep.get("variants", {})
    flags = []
    ctl = v.get("cert-lambda-plain")
    if rep.get("replay_nonzero_classes"):
        flags.append("CONTROL_FAIL")
    elif ctl is not None and Fraction(ctl.get("lb_exact", "0/1")) < 1 - OWN_GAIN_MARGIN:
        flags.append("CONTROL_FAIL")
    out = "NO_GAIN"
    claimed = rep.get("claimed_C")
    own = 1 / Fraction(claimed) if claimed else Fraction(1, 2)
    for name, info in v.items():
        if "lb_exact" not in info or not info.get("symmetric"):
            continue
        lb = Fraction(info["lb_exact"])
        if lb > Fraction(F.KLSS_W) + Fraction(1, 10 ** 9):
            flags.append("UNSOUND")
        if lb > F.RECORD_W:
            out = "F3_RECORD"
        elif lb > own + OWN_GAIN_MARGIN and out == "NO_GAIN":
            out = "F3_GAIN"
    for w in ("UNSOUND", "CONTROL_FAIL"):
        if w in flags:
            return w + "+" + out
    return out


def _write(out_dir, rep):
    with open(os.path.join(out_dir, "results.json"), "w") as fh:
        json.dump(rep, fh, indent=1)


def summary_md(rep):
    L = ["# f3cert gate run: %s on %s" % (rep["plan"], rep.get("config") or "?"), "",
         "Made with AI agents working in MV2's name (MV2 of Munim, Inc.); not checked by a human",
         "mathematician. Pre-registration: f3cert/PREREG.md. Certificate data: Farnamfar,",
         "arXiv:2611.19594 ancillary files (CC BY 4.0), SHA-256 %s." % (rep.get("sha256") or "-"), "",
         "**Verdict: %s**" % rep.get("verdict"), "",
         "Every bound below is exact (recomputed in rational arithmetic from the LP's dual vector)",
         "and is a lower bound on w = h(x)/h(d) in the symmetric (rotation-trick) setting, so",
         "beta_3 >= 3^w. Reference values: own certificate 1/C, record 1/1.8263483657 = 0.547540,",
         "KLSS ceiling 0.579380 (no sound bound may exceed it). Status 'optimal-all' means the LP",
         "reached its optimum over the whole row pool; otherwise the bound is valid but may not be",
         "the LP optimum.", "",
         "| variant | status | exact bound | decimal | base 3^w | rows used | seconds |",
         "|---|---|---|---|---|---|---|"]
    for name, info in rep.get("variants", {}).items():
        if "lb_exact" not in info:
            L.append("| %s | error | - | - | - | - | - |" % name)
            continue
        q = Fraction(info["lb_exact"])
        L.append("| %s | %s | %s | %.7f | %.6f | %d | %s |" % (
            name, info["status"], "%d/%d" % (q.numerator, q.denominator) if q.denominator < 10 ** 6
            else "(see results.json)", info["lb"], info["base"], info["rows_used"],
            info["seconds"]))
    L += ["", "Replay of the certificate's own identity: %s non-zero residual classes, %s rows "
          "not rebuilt." % (rep.get("replay_nonzero_classes"), rep.get("replay_unknown_rows")),
          "Claimed C of the certificate: %s." % rep.get("claimed_C"), ""]
    return "\n".join(L) + "\n"


def fetch(name, data_dir):
    """The certificate JSON from data_dir if cached there, else from arXiv (then cached)."""
    return F.load_cert(name, data_dir)
