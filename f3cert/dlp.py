# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""A pure-standard-library dual simplex with cutting planes, and exact rational lower bounds.

Problem.  minimise  cost . h  over  h >= 0  subject to rows  a . h + const >= 0,
with every cost coefficient >= 0 (all our objectives are entropies).

Why the dual simplex.  With cost >= 0 the all-slack basis is dual feasible, so no phase I is
needed, rows can be added at any time (cutting planes), and EVERY iterate is dual feasible: the
current dual vector y >= 0 proves cost . h >= z at every step, not only at the optimum.  The
solver works in floating point, but no number it returns is trusted: exact_bound() rounds the
dual vector to rationals, clips it to y >= 0 and recomputes the bound in exact arithmetic,

    cost . h  =  sum_i y_i (a_i . h + const_i)  -  sum_i y_i const_i  +  r . h
              >= -sum_i y_i const_i + sum_c min(r_c lo_c, r_c hi_c),     r = cost - sum_i y_i a_i,

which is valid for ANY y >= 0 as long as every row holds and lo_c <= h_c <= hi_c.  So a bug or a
rounding error in the simplex can only make the certified bound weaker, never wrong.

Tableau (compact form).  Row i reads  x_B(i) + sum_j T[i][j] x_N(j) = rhs[i];  the objective
is  z + sum_j d[j] x_N(j)  (d = reduced costs >= 0).  A row variable ('s', rid) is the slack
a . h + const of pool row rid; ('h', key) is an entropy variable."""
import random
import time
from fractions import Fraction


class DualSimplex:
    def __init__(self, cost, piv_tol=1e-9, feas_tol=1e-9, seed=0):
        for k, v in cost.items():
            if v < 0:
                raise ValueError("negative cost coefficient for %r" % (k,))
        self.cost = {k: float(v) for k, v in cost.items()}
        self.T = []
        self.rhs = []
        self.d = []
        self.nb = []        # slot -> variable
        self.bv = []        # row -> variable
        self.pos_nb = {}
        self.pos_b = {}
        self.z = 0.0
        self.pivots = 0
        self.piv_tol = piv_tol
        self.feas_tol = feas_tol
        self.rng = random.Random(seed)

    # -------------------------------------------------------------- building
    def _add_col(self, key):
        var = ("h", key)
        self.pos_nb[var] = len(self.nb)
        self.nb.append(var)
        self.d.append(self.cost.get(key, 0.0))
        for row in self.T:
            row.append(0.0)

    def has_row(self, rid):
        var = ("s", rid)
        return var in self.pos_nb or var in self.pos_b

    def add_row(self, rid, coeffs, const):
        """Add the row  sum coeffs[key] h_key + const >= 0  with its slack basic."""
        for key in coeffs:
            var = ("h", key)
            if var not in self.pos_nb and var not in self.pos_b:
                self._add_col(key)
        new = [0.0] * len(self.nb)
        rhs = float(const)
        for key, a in coeffs.items():
            a = float(a)
            if a == 0.0:
                continue
            var = ("h", key)
            j = self.pos_nb.get(var)
            if j is not None:
                new[j] -= a
            else:
                i = self.pos_b[var]
                new = [x + a * t for x, t in zip(new, self.T[i])]
                rhs += a * self.rhs[i]
        var = ("s", rid)
        self.pos_b[var] = len(self.T)
        self.bv.append(var)
        self.T.append(new)
        self.rhs.append(rhs)

    # -------------------------------------------------------------- pivoting
    def pivot(self, r, k):
        T = self.T
        rowr = T[r]
        p = rowr[k]
        inv = 1.0 / p
        newr = [t * inv for t in rowr]
        newr[k] = inv
        rr = self.rhs[r] * inv
        rhs = self.rhs
        for i in range(len(T)):
            if i == r:
                continue
            rowi = T[i]
            f = rowi[k]
            if f == 0.0:
                continue
            if -1e-13 < f < 1e-13:
                rowi[k] = 0.0
                continue
            nr = [a - f * b for a, b in zip(rowi, newr)]
            nr[k] = -f * inv
            T[i] = nr
            rhs[i] -= f * rr
        T[r] = newr
        rhs[r] = rr
        dk = self.d[k]
        if dk != 0.0:
            d = [a - dk * b for a, b in zip(self.d, newr)]
            d[k] = -dk * inv
            self.d = d
            self.z += dk * rr
        ent, lev = self.nb[k], self.bv[r]
        self.nb[k] = lev
        self.bv[r] = ent
        del self.pos_nb[ent]
        del self.pos_b[lev]
        self.pos_nb[lev] = k
        self.pos_b[ent] = r
        self.pivots += 1

    def run(self, deadline, max_pivots=None):
        """Dual simplex until primal feasible ('optimal'), 'infeasible', 'time' or 'pivots'."""
        stall = 0
        last_z = self.z
        start = self.pivots
        while True:
            if time.time() > deadline:
                return "time"
            if max_pivots is not None and self.pivots - start >= max_pivots:
                return "pivots"
            rhs = self.rhs
            viol = [i for i, v in enumerate(rhs) if v < -self.feas_tol]
            if not viol:
                return "optimal"
            if stall > 60:
                r = self.rng.choice(viol)
            else:
                r = min(viol, key=lambda i: rhs[i])
            row = self.T[r]
            d = self.d
            k = -1
            best = 0.0
            mag = 0.0
            for j, a in enumerate(row):
                if a < -self.piv_tol:
                    dj = d[j] if d[j] > 0.0 else 0.0
                    ratio = dj / -a
                    if k < 0 or ratio < best - 1e-12 or (ratio <= best + 1e-12 and -a > mag):
                        k, best, mag = j, ratio, -a
            if k < 0:
                return "infeasible"
            self.pivot(r, k)
            if self.z > last_z + 1e-12:
                last_z = self.z
                stall = 0
            else:
                stall += 1

    # -------------------------------------------------------------- read-out
    def primal(self):
        out = {}
        for i, var in enumerate(self.bv):
            if var[0] == "h":
                out[var[1]] = self.rhs[i]
        return out

    def duals(self):
        out = {}
        for j, var in enumerate(self.nb):
            if var[0] == "s" and self.d[j] > 0.0:
                out[var[1]] = self.d[j]
        return out


def solve(cost, rows, init, deadline, batch=80, viol_tol=1e-7, seed=0, log=None):
    """Cutting-plane LP: start with the rows whose indices are in init, then repeatedly add the
    most violated pool rows.  rows[i] = (coeffs dict, const).  Never raises on time-out: the
    returned duals are always dual feasible, hence give a valid bound via exact_bound()."""
    ds = DualSimplex(cost, seed=seed)
    added = set()
    for idx in init:
        if idx not in added:
            ds.add_row(idx, rows[idx][0], rows[idx][1])
            added.add(idx)
    fl = [([(k, float(a)) for k, a in co.items()], float(c)) for co, c in rows]
    rounds = 0
    status = "optimal"
    while True:
        status = ds.run(deadline)
        if status != "optimal":
            break
        h = ds.primal()
        viol = []
        for idx, (co, c) in enumerate(fl):
            if idx in added:
                continue
            v = c
            for k, a in co:
                v += a * h.get(k, 0.0)
            if v < -viol_tol:
                viol.append((v, idx))
        if not viol:
            status = "optimal-all"
            break
        viol.sort()
        for _v, idx in viol[:batch]:
            ds.add_row(idx, rows[idx][0], rows[idx][1])
            added.add(idx)
        rounds += 1
        if log:
            log("  round %d: z=%.9f rows=%d cols=%d pivots=%d violated=%d" % (
                rounds, ds.z, len(added), len(ds.nb), ds.pivots, len(viol)))
    return {"status": status, "z": ds.z, "duals": ds.duals(), "pivots": ds.pivots,
            "rows_in_lp": len(added), "cols": len(ds.nb), "rounds": rounds,
            "primal": ds.primal()}


def exact_bound(cost, rows, duals, box, den=10 ** 9):
    """Exact rational lower bound on min cost . h from ANY dual vector (see module doc).
    box(key) -> (lo, hi) must hold for every variable.  Returns (bound, used, boxused)."""
    r = {k: Fraction(v) for k, v in cost.items()}
    val = Fraction(0)
    used = []
    for idx in sorted(duals):
        q = Fraction(duals[idx]).limit_denominator(den)
        if q <= 0:
            continue
        co, c = rows[idx]
        val -= q * Fraction(c)
        for k, a in co.items():
            r[k] = r.get(k, Fraction(0)) - q * Fraction(a)
        used.append((idx, q))
    boxused = []
    for k, rv in r.items():
        if rv == 0:
            continue
        lo, hi = box(k)
        if rv > 0:
            val += rv * Fraction(lo)
        else:
            val += rv * Fraction(hi)
            boxused.append((k, rv, hi))
    return val, used, boxused
