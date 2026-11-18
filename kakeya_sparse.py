"""kakeya_sparse.py -- the Kakeya-restricted entropy LP over F_3 on large page configurations.

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
Licence: Apache-2.0. Pre-registration: notes/prereg-kakeya-sparse.md.

Why. kakeya_lp.py enumerates every subset of at most 14 atoms, so it cannot reach the
30- and 108-vertex page configurations of A. Farnamfar (arXiv:2611.19594). His Shannon-only
certificates prove the sum-difference inequality H(X,Y) <= a H(X) + b H(Y) + c H(X+Y) for
difference-injective pairs in every abelian group, with a + b + c = 152/83 (five pages) and
2762/1509 (eighteen pages). Over F_3 a line is a 3-term progression, and the argument of
note a180 turns any such inequality into a Kakeya bound |K| >= 3^(n / (a + b + c) - o(n)).

This module
  1. rebuilds Farnamfar's configurations over F_3 (a closure is an F_3-span plus the
     d-rule "x_v, y_v are determined once d_v = y_v - x_v is"),
  2. puts his rows into an LP whose variables are F_3 closures, and
  3. re-optimises over a sparse neighbourhood of Shannon rows around his certificate, with
     the Kakeya restriction (every single G-valued form has entropy <= log|G|) on cross forms.
The independent replay of his certificates and the exact check of every certificate this
module finds are in sparse_cert_check.py (its own F_3 algebra).

Units: entropies are in units of log|G|, G = F_3^k. Every vertex is a Kakeya pair
(x, y) = (P(X), P(X) + X) with X uniform on G, so H(x_v, y_v) = 1 ("norm"). By the
rotation argument of kakeya_lp.py every reading x_v, y_v, s_v of every vertex may be set
to one value t ("read"). The LP minimises t; a certificate with t >= c proves
(H(x) + H(y) + H(s)) / 3 >= c log|G| for every map of every F_3^k, hence beta_3 >= 3^c.
"""

import argparse
import itertools
import json
import os
import sys
import time
from fractions import Fraction

import kakeya_lp as klp

KT_BOUND = Fraction(6, 11)
FARN_SHANNON = Fraction(83, 152)
FARN_RECORD = Fraction(114631769327023765, 209357544569848128)  # 1 / 1.8263483657...

READ_AB = {"x": (1, 0), "y": (0, 1), "s": (1, 1), "d": (2, 1)}  # d = y - x
KINDS = ("x", "y", "s", "d")

# ----------------------------------------------------------------------------------------
# Forms. A "combo" is a sorted tuple of (vertex, a, b): the form sum a x_v + b y_v (mod 3).
# ----------------------------------------------------------------------------------------


def norm_combo(terms):
    acc = {}
    for v, a, b in terms:
        pa, pb = acc.get(v, (0, 0))
        acc[v] = ((pa + a) % 3, (pb + b) % 3)
    return tuple(sorted((v, a, b) for v, (a, b) in acc.items() if a or b))


def std(v, r):
    a, b = READ_AB[r]
    return ((v, a, b),)


def slope_kind(a, b):
    """Reading kind whose F_3-span equals that of a x + b y."""
    a, b = a % 3, b % 3
    if a == 0 and b == 0:
        raise ValueError("zero slope")
    lead = a if a else b
    if lead == 2:
        a, b = (2 * a) % 3, (2 * b) % 3
    return {(1, 0): "x", (0, 1): "y", (1, 1): "s", (1, 2): "d"}[(a, b)]


def farn_form(f):
    """Farnamfar's standard form [v, [a, b]] -> combo. Extra forms ["amb", k] raise."""
    if (not isinstance(f, (list, tuple)) or len(f) != 2 or isinstance(f[0], bool)
            or not isinstance(f[0], int) or not isinstance(f[1], (list, tuple))
            or len(f[1]) != 2):
        raise ValueError("unsupported form %r" % (f,))
    c = norm_combo([(int(f[0]), int(f[1][0]), int(f[1][1]))])
    if not c:
        raise ValueError("zero form %r" % (f,))
    return c


def farn_word(cert):
    """Farnamfar's 'steps' (U = copied vertices, V = glue readings) as a kakeya_lp word."""
    steps = []
    for st in cert["steps"]:
        glue = [[int(v), slope_kind(int(sl[0]), int(sl[1]))] for v, sl in st["V"]]
        steps.append({"block": [int(u) for u in st["U"]], "glue": glue})
    return {"steps": steps}


def combo_json(c):
    return [list(t) for t in c]


# ----------------------------------------------------------------------------------------
# The sparse model
# ----------------------------------------------------------------------------------------


class SparseModel:
    """Rows (sense, {var: int}, const, desc) as in kakeya_lp.Model, so kakeya_lp.combine,
    kakeya_lp.exact_solve and kakeya_lp.certificate_from_duals apply unchanged.
    Variable 0 is the empty closure, variable 1 is t."""

    def __init__(self, word):
        self.word = word
        self.cfg = klp.Config(word)
        self.R = self.cfg.r
        self.verts = self.cfg.vertices()
        self.nvert = len(self.verts)
        self.keys = [(), "t"]
        self.key_index = {(): 0, "t": 1}
        self.t = 1
        self.gen = {}
        self.rows = []
        self._sig = {}
        self._cl = {}
        self.new_of = [dict(zip(st["block"], st["new"])) for st in self.cfg.steps]
        self.old_of = [dict(zip(st["new"], st["block"])) for st in self.cfg.steps]

    def nvars(self):
        return len(self.keys)

    def vec(self, combo):
        out = [0] * self.R
        for v, a, b in combo:
            x, y = self.verts[v]
            for i in range(self.R):
                out[i] = (out[i] + a * x[i] + b * y[i]) % 3
        return tuple(out)

    def key(self, combos):
        sig = frozenset(combos)
        k = self._cl.get(sig)
        if k is None:
            k = klp.closure([self.vec(c) for c in sig], self.verts)
            self._cl[sig] = k
            if k not in self.gen:
                self.gen[k] = tuple(sorted(sig))
        return k

    def var(self, combos):
        k = self.key(combos)
        idx = self.key_index.get(k)
        if idx is None:
            idx = len(self.keys)
            self.key_index[k] = idx
            self.keys.append(k)
        return idx

    def add_row(self, sense, terms, const, desc):
        """Adds the row; returns its index (an existing index for a duplicate) or None for
        an identically zero row."""
        coefs = {}
        for var, c in terms:
            if var == 0 or c == 0:
                continue
            coefs[var] = coefs.get(var, 0) + c
        coefs = {k: v for k, v in coefs.items() if v}
        if not coefs and const == 0:
            return None
        sig = (sense, tuple(sorted(coefs.items())), const)
        if sig in self._sig:
            return self._sig[sig]
        self._sig[sig] = len(self.rows)
        self.rows.append((sense, coefs, const, desc))
        return len(self.rows) - 1

    # --- row kinds ---
    def add_sub(self, K, i, j):
        """I(i; j | K) >= 0."""
        K = frozenset(K)
        if i == j or i in K or j in K:
            return None
        return self.add_row("ge", [(self.var(K | {i}), 1), (self.var(K | {j}), 1),
                                   (self.var(K | {i, j}), -1), (self.var(K), -1)], 0,
                            ("sub", tuple(sorted(K)), i, j))

    def add_mono(self, K, i):
        """H(K, i) - H(K) >= 0."""
        K = frozenset(K)
        if i in K:
            return None
        return self.add_row("ge", [(self.var(K | {i}), 1), (self.var(K), -1)], 0,
                            ("mono", tuple(sorted(K)), i))

    def copy_sets(self, s):
        st = self.cfg.steps[s]
        old = [std(v, r) for v in range(st["old_n"]) for r in ("x", "y")]
        new = [std(v, r) for v in st["new"] for r in ("x", "y")]
        glue = [std(v, k) for v, k in st["glue"]]
        return old, new, glue

    def add_copy(self, s):
        """I(Old; New | glue) = 0 (copy lemma)."""
        old, new, glue = self.copy_sets(s)
        return self.add_row("eq", [(self.var(old + new), 1), (self.var(glue), 1),
                                   (self.var(old), -1), (self.var(new), -1)], 0, ("copy", s))

    def add_copy_rows(self):
        for s in range(len(self.cfg.steps)):
            self.add_copy(s)

    def image(self, s, combos, back=False):
        m = self.old_of[s] if back else self.new_of[s]
        out = []
        for c in combos:
            if any(v not in m for v, _, _ in c):
                return None
            out.append(norm_combo([(m[v], a, b) for v, a, b in c]))
        return out

    def add_law(self, s, combos):
        """H(S) = H(S') for forms S on the vertices copied at step s and their copies S'."""
        combos = list(combos)
        img = self.image(s, combos)
        if img is None:
            return None
        return self.add_row("eq", [(self.var(combos), 1), (self.var(img), -1)], 0,
                            ("law", s, tuple(sorted(set(combos)))))

    def add_law_orbits(self, rounds=2, cap=None):
        """Law rows from every existing variable to its copies and originals."""
        added = 0
        frontier = list(self.keys[2:])
        for _ in range(rounds):
            nxt = []
            for k in frontier:
                gens = self.gen.get(k)
                if not gens:
                    continue
                for s in range(len(self.cfg.steps)):
                    for back in (False, True):
                        img = self.image(s, gens, back)
                        if img is None:
                            continue
                        src = img if back else list(gens)
                        n0, r0 = len(self.keys), len(self.rows)
                        self.add_law(s, src)
                        added += len(self.rows) - r0
                        nxt.extend(self.keys[n0:])
                        if cap is not None and added >= cap:
                            return added
            frontier = nxt
        return added

    def add_norm(self, v):
        return self.add_row("eq", [(self.var([std(v, "x"), std(v, "y")]), 1)], -1, ("norm", v))

    def add_read(self, v, r):
        return self.add_row("eq", [(self.var([std(v, r)]), 1), (self.t, -1)], 0, ("read", v, r))

    def add_norm_read(self):
        for v in range(self.nvert):
            self.add_norm(v)
            for r in ("x", "y", "s"):
                self.add_read(v, r)

    def add_unif(self, combo):
        """Kakeya restriction: H(f) <= log|G| for a single G-valued form f."""
        return self.add_row("ge", [(self.var([combo]), -1)], 1, ("unif", combo))

    def add_farn_rows(self, cert):
        """Farnamfar's sub/mono rows and equal-law generators. Returns the base list
        [(K, i, j)] of his sub rows (for the neighbourhood tiers)."""
        base = []
        for row in cert["rows"]:
            typ = row.get("type")
            if typ == "sub":
                K = frozenset(farn_form(f) for f in row["K"])
                i, j = farn_form(row["i"]), farn_form(row["j"])
                self.add_sub(K, i, j)
                base.append((K, i, j))
            elif typ == "mono":
                K = frozenset(farn_form(f) for f in row["K"])
                self.add_mono(K, farn_form(row["i"]))
            elif typ == "ci":
                self.add_copy(int(row["step"]))
            else:
                raise ValueError("unsupported row type %r" % (typ,))
        for e in cert.get("eqlaw", []):
            self.add_law(int(e["step"]), [farn_form(f) for f in e["gens"]])
        return base


# ----------------------------------------------------------------------------------------
# Neighbourhood tiers around a base list of sub rows
# ----------------------------------------------------------------------------------------


def row_vertices(K, i, j):
    vs = set()
    for c in list(K) + [i, j]:
        for v, _, _ in c:
            vs.add(v)
    return sorted(vs)


def local_forms(vs):
    return [std(v, r) for v in vs for r in KINDS]


def cross_forms(vs):
    out = []
    for v, w in itertools.combinations(vs, 2):
        for r in KINDS:
            a, b = READ_AB[r]
            out.append(norm_combo([(v, a, b), (w, -a, -b)]))
            out.append(norm_combo([(v, a, b), (w, a, b)]))
    return out


def _stop(M, deadline, max_rows):
    return time.time() > deadline or len(M.rows) > max_rows


def tier_A(M, base, deadline, max_rows):
    """Same conditioning set K, every pair of local standard forms."""
    for K, i, j in base:
        nf = [f for f in local_forms(row_vertices(K, i, j)) if f not in K]
        for f in nf:
            M.add_mono(K, f)
        for a, b in itertools.combinations(nf, 2):
            M.add_sub(K, a, b)
        if _stop(M, deadline, max_rows):
            return False
    return True


def tier_B(M, base, deadline, max_rows):
    """K with one form removed or one local form added, every pair of local forms."""
    for K, i, j in base:
        nf = local_forms(row_vertices(K, i, j))
        variants = [K - {g} for g in K] + [K | {f} for f in nf if f not in K]
        for K2 in variants:
            rest = [f for f in nf if f not in K2]
            for a, b in itertools.combinations(rest, 2):
                M.add_sub(K2, a, b)
            if _stop(M, deadline, max_rows):
                return False
    return True


def tier_C(M, base, deadline, max_rows):
    """Cross forms r_v +- r_w between vertices of a base row: the Kakeya restriction
    H(cross) <= 1, and Shannon rows pairing them with local forms."""
    for K, i, j in base:
        vs = row_vertices(K, i, j)
        nf = [f for f in local_forms(vs) if f not in K]
        for c in cross_forms(vs):
            if c in K:
                continue
            M.add_unif(c)
            M.add_mono(K, c)
            for f in nf:
                M.add_sub(K, c, f)
        if _stop(M, deadline, max_rows):
            return False
    return True


# ----------------------------------------------------------------------------------------
# Solving and certificates
# ----------------------------------------------------------------------------------------


class RowView:
    """A model restricted to a list of rows (same variables)."""

    def __init__(self, model, rows):
        self.rows = rows
        self.t = model.t
        self._n = model.nvars()

    def nvars(self):
        return self._n


def desc_json(desc):
    k = desc[0]
    if k == "sub":
        return {"k": "sub", "K": [combo_json(c) for c in desc[1]], "i": combo_json(desc[2]),
                "j": combo_json(desc[3])}
    if k == "mono":
        return {"k": "mono", "K": [combo_json(c) for c in desc[1]], "i": combo_json(desc[2])}
    if k == "copy":
        return {"k": "copy", "step": desc[1]}
    if k == "law":
        return {"k": "law", "step": desc[1], "S": [combo_json(c) for c in desc[2]]}
    if k == "norm":
        return {"k": "norm", "v": desc[1]}
    if k == "read":
        return {"k": "read", "v": desc[1], "r": desc[2]}
    if k == "unif":
        return {"k": "unif", "f": combo_json(desc[1])}
    raise ValueError(k)


def export(model, view, bound, mults, uniform):
    return {
        "format": "kakeya-sparse-certificate-1",
        "word": model.word,
        "uniform": bool(uniform),
        "claimed_bound": str(bound),
        "rows": [{"d": desc_json(view.rows[ri][3]), "m": str(mu)}
                 for ri, mu in sorted(mults.items()) if mu != 0],
    }


def solve(view, time_limit=None):
    import numpy as np
    from scipy.optimize import linprog
    from scipy.sparse import csr_matrix

    nv = view.nvars()
    ub_r, ub_c, ub_v, b_ub = [], [], [], []
    eq_r, eq_c, eq_v, b_eq = [], [], [], []
    for sense, coefs, const, _ in view.rows:
        if sense == "ge":
            i = len(b_ub)
            for var, a in coefs.items():
                ub_r.append(i)
                ub_c.append(var)
                ub_v.append(-a)
            b_ub.append(const)
        else:
            i = len(b_eq)
            for var, a in coefs.items():
                eq_r.append(i)
                eq_c.append(var)
                eq_v.append(a)
            b_eq.append(-const)
    A_ub = csr_matrix((ub_v, (ub_r, ub_c)), shape=(len(b_ub), nv))
    A_eq = csr_matrix((eq_v, (eq_r, eq_c)), shape=(len(b_eq), nv))
    c = np.zeros(nv)
    c[view.t] = 1.0
    bounds = [(None, None)] * nv
    bounds[0] = (0, 0)
    opts = {}
    if time_limit is not None:
        opts["time_limit"] = float(max(60.0, time_limit))
    res = linprog(c, A_ub=A_ub, b_ub=np.array(b_ub, dtype=float), A_eq=A_eq,
                  b_eq=np.array(b_eq, dtype=float), bounds=bounds, method="highs",
                  options=opts)
    if res.status != 0:
        return None, None, None, res.message
    ge_mu = [-float(x) for x in res.ineqlin.marginals]
    eq_mu = [float(x) for x in res.eqlin.marginals]
    return float(res.fun), ge_mu, eq_mu, "ok"


def solve_and_certify(model, rows, tag, out_dir, want_cert, log, time_limit=None):
    import sparse_cert_check as scc

    view = RowView(model, rows)
    t0 = time.time()
    try:
        val, ge_mu, eq_mu, msg = solve(view, time_limit)
    except MemoryError:
        val, ge_mu, eq_mu, msg = None, None, None, "MemoryError"
    rec = {"tag": tag, "rows": len(rows), "vars": model.nvars(), "value": val,
           "msg": str(msg), "solve_s": round(time.time() - t0, 1),
           "unif_rows": sum(1 for r in rows if r[3][0] == "unif")}
    if val is not None and want_cert(val):
        uniform = rec["unif_rows"] > 0
        got, why = None, "no sign convention worked"
        for sg, se in ((1, 1), (1, -1), (-1, 1), (-1, -1)):
            bound, mults = klp.certificate_from_duals(view, [sg * x for x in ge_mu],
                                                      [se * x for x in eq_mu])
            if bound is not None:
                got = (bound, mults)
                break
            why = mults
        if got is None:
            rec["certificate"] = "failed: %s" % why
        else:
            bound, mults = got
            cert = export(model, view, bound, mults, uniform)
            rec["exact_bound"] = str(bound)
            rec["exact_float"] = float(bound)
            rec["cert_rows"] = len(cert["rows"])
            try:
                checked = scc.check(cert)
                rec["checked_bound"] = str(checked)
                rec["checked_float"] = float(checked)
            except Exception as e:  # noqa: BLE001 -- record any checker rejection
                rec["checker_error"] = repr(e)
            name = "cert_%s.json" % tag
            with open(os.path.join(out_dir, name), "w") as fh:
                json.dump(cert, fh)
            rec["certificate"] = name
    log(rec)
    return rec


# ----------------------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------------------


def run_file(path, out_dir, deadline, max_rows, log):
    import sparse_cert_check as scc

    with open(path) as fh:
        cert = json.load(fh)
    name = os.path.splitext(os.path.basename(path))[0]
    rec = {"file": os.path.basename(path), "claimed_C": cert.get("claimed_C"),
           "lambda": cert.get("lambda"), "n_rows": len(cert.get("rows", [])),
           "n_steps": len(cert.get("steps", [])), "n_extra": len(cert.get("extra") or [])}
    try:
        rec["replay"] = scc.farn_replay(cert)
    except Exception as e:  # noqa: BLE001
        rec["replay"] = {"ok": False, "error": repr(e)}
    log({"tag": name + "-replay", "replay": rec["replay"]})
    if cert.get("extra"):
        rec["lp"] = "skipped: extra (cross) forms are not supported"
        return rec
    try:
        M = SparseModel(farn_word(cert))
        M.add_copy_rows()
        M.add_norm_read()
        base = M.add_farn_rows(cert)
    except (ValueError, KeyError) as e:
        rec["lp"] = "model failed: %r" % (e,)
        return rec
    rec["vertices"] = M.nvert
    rec["R"] = M.R
    tiers = {}

    def left():
        return deadline - time.time()

    always = lambda v: True  # noqa: E731
    hit = lambda v: v > float(FARN_SHANNON) + 1e-7  # noqa: E731
    tiers["t0"] = solve_and_certify(M, list(M.rows), name + "-t0", out_dir, always, log, left())
    M.add_law_orbits(rounds=2, cap=max_rows // 4)
    tiers["t0L"] = solve_and_certify(M, list(M.rows), name + "-t0L", out_dir, hit, log, left())
    for tname, fn in (("tA", tier_A), ("tB", tier_B)):
        if left() < 300:
            break
        complete = fn(M, base, deadline - 240, max_rows)
        M.add_law_orbits(rounds=1, cap=max_rows // 4)
        tiers[tname] = solve_and_certify(M, list(M.rows), name + "-" + tname, out_dir, hit,
                                         log, left())
        tiers[tname]["tier_complete"] = complete
    if left() > 300:
        complete = tier_C(M, base, deadline - 240, max_rows)
        M.add_law_orbits(rounds=1, cap=max_rows // 4)
        rows_u = list(M.rows)
        rows_n = [r for r in rows_u if r[3][0] != "unif"]
        tiers["tC-n"] = solve_and_certify(M, rows_n, name + "-tC-n", out_dir, hit, log, left())
        if left() > 120:
            tiers["tC-u"] = solve_and_certify(M, rows_u, name + "-tC-u", out_dir, hit, log,
                                              left())
            tiers["tC-u"]["tier_complete"] = complete
    keep = ("rows", "vars", "value", "msg", "exact_bound", "checked_bound", "checked_float",
            "checker_error", "certificate", "unif_rows", "tier_complete", "solve_s")
    rec["tiers"] = {k: {kk: v.get(kk) for kk in keep if kk in v} for k, v in tiers.items()}
    return rec


def decide(records):
    best, best_tag = None, None
    for r in records:
        for tname, t in (r.get("tiers") or {}).items():
            cb = t.get("checked_bound")
            if cb is not None and (best is None or Fraction(cb) > best):
                best, best_tag = Fraction(cb), "%s/%s" % (r["file"], tname)
    if best is None:
        verdict = "NO_CERTIFICATE"
    elif best > FARN_RECORD:
        verdict = "RECORD"
    elif best > FARN_SHANNON:
        verdict = "SHANNON_GAIN"
    else:
        verdict = "NULL"
    return {"best_checked": None if best is None else str(best),
            "best_checked_float": None if best is None else float(best),
            "best_base": None if best is None else 3 ** float(best),
            "best_tag": best_tag, "verdict": verdict}


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--cert-dir", required=True)
    ap.add_argument("--files", nargs="*", default=["standard-five-page.json", "standard.json"])
    ap.add_argument("--out-dir", default="out")
    ap.add_argument("--minutes", type=float, default=150.0)
    ap.add_argument("--max-rows", type=int, default=400000)
    a = ap.parse_args(argv)
    os.makedirs(a.out_dir, exist_ok=True)
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    start = time.time()
    logf = open(os.path.join(a.out_dir, "results.jsonl"), "w")

    def log(rec):
        logf.write(json.dumps(rec, default=str) + "\n")
        logf.flush()
        print(json.dumps(rec, default=str)[:400], flush=True)

    shares = [0.7, 0.3] + [0.0] * max(0, len(a.files) - 2)
    records = []
    for fname, share in zip(a.files, shares):
        path = os.path.join(a.cert_dir, fname)
        if not os.path.exists(path):
            records.append({"file": fname, "missing": True})
            continue
        spent = time.time() - start
        budget = max(0.0, 60 * a.minutes - spent) if share == shares[-1] else 60 * a.minutes * share
        deadline = time.time() + budget
        records.append(run_file(path, a.out_dir, deadline, a.max_rows, log))
    summary = {
        "files": records,
        "thresholds": {"kt": str(KT_BOUND), "farnamfar_shannon": str(FARN_SHANNON),
                       "farnamfar_record": str(FARN_RECORD)},
        "decision": decide(records),
        "minutes": round((time.time() - start) / 60, 1),
    }
    with open(os.path.join(a.out_dir, "summary.json"), "w") as fh:
        json.dump(summary, fh, indent=1, default=str)
    logf.close()
    print(json.dumps(summary["decision"], indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
