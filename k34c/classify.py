# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""k34c, phase 1: list every Kakeya set of F_4^3 with 28 points (the minimum, K(3, 4) = 28).

Question (pre-registered in k34c/PLAN.md): is the 28-point Kopparty-Saraf-Sudan set the only
smallest Kakeya set of F_4^3 up to affine maps and the field automorphism, and if not, what are
the others?

Method. It reuses the search of k34b/indep.py (the independently written second route to
K(3, 4) = 28) with the threshold T = 29, so every branch whose lower bound is at most 28 is
explored. At each complete map f it does not stop at the optimal value: it lists every
placement of the five horizontal lines that reaches the optimum and records each resulting
point set (a 64-bit mask, bit 16 z + 4 x + y for the point (x, y, z)).

Why this finds every 28-point Kakeya set (see PLAN.md for the full argument):
* a 28-point Kakeya set K is a union of one line per direction (any such union is a Kakeya
  subset, and 27 points are too few);
* a smallest plane of K has at most 6 points (if every plane had 7 or more, every plane would
  have exactly 7, but then sum over the 84 planes of x(x - 1) would be 3,528, while it must be
  28 * 27 * 5 = 3,780);
* move that plane to z = 0; the image S0' of f (the points where the 16 non-horizontal lines
  meet z = 0) has r' <= 6 points, it is moved to its orbit representative, a shear fixes
  f(0) = S0'[0], and the bound of k34b stays valid with r' (every plane has >= r >= r' points);
* K contains the union of the forced points and one line per horizontal direction, which has
  at least the leaf's optimal value 28 points, so K is exactly one of the optimal placements
  listed at that leaf.
Phase 2 (a later run) sorts the listed sets into classes under the full 3-D group."""
import itertools
import json
import os
import sys
import time

_HERE = os.path.dirname(os.path.abspath(__file__))
for _p in (_HERE, os.path.normpath(os.path.join(_HERE, os.pardir, "k34b")),
           r"E:\MV2-Pursuit\work\20261128T072812Z-mathematics\gate\k34b"):
    if _p not in sys.path and os.path.isfile(os.path.join(_p, "indep.py")):
        sys.path.append(_p)

import indep  # noqa: E402

RMAX = {3: 4, 4: 6}
MADE_WITH = "AI agents working in MV2's name; not checked by a human mathematician"


def _pc(m):
    return bin(m).count("1")


def mask_points(m, q):
    """Points (x, y, z) of a 3-D mask; bit n z + q x + y, n = q * q."""
    n = q * q
    return [[(i % n) // q, (i % n) % q, i // n] for i in range(n * q) if (m >> i) & 1]


def points_mask(points, q):
    n = q * q
    m = 0
    for x, y, z in points:
        m |= 1 << (n * z + q * x + y)
    return m


class EnumSearch(indep.Search):
    """k34b's search; every leaf below T lists all optimal point sets."""

    def __init__(self, P, S0, T, prefix=(), deadline=None):
        super().__init__(P, S0, T, prefix=prefix, deadline=deadline)
        self.sets = set()
        self.hist = {}
        self.below = 0
        self.ocache = {}

    def plane_opts(self, mask):
        """best[D], opts[D]: fewest points of mask plus one line of each horizontal direction
        in D, and every union mask that reaches it."""
        c = self.ocache.get(mask)
        if c is not None:
            return c
        if len(self.ocache) > 200000:
            self.ocache.clear()
        HL = self.P.hlines
        nd = len(HL)
        reach = {0: {mask}}
        best = [0] * (1 << nd)
        opts = [None] * (1 << nd)
        best[0] = _pc(mask)
        opts[0] = [mask]
        for D in range(1, 1 << nd):
            low = (D & -D).bit_length() - 1
            cur = set()
            for m in reach[D & ~(1 << low)]:
                for line in HL[low]:
                    cur.add(m | line)
            reach[D] = cur
            b = min(_pc(m) for m in cur)
            best[D] = b
            opts[D] = sorted(m for m in cur if _pc(m) == b)
        c = (best, opts)
        self.ocache[mask] = c
        return c

    def optimal_sets(self, masks, val):
        nd = len(self.P.hlines)
        npl = len(masks)
        n = self.P.n
        tabs = [self.plane_opts(m) for m in masks]
        out = set()
        lo = None
        for assign in itertools.product(range(npl), repeat=nd):
            D = [0] * npl
            for d, k in enumerate(assign):
                D[k] |= 1 << d
            tot = 0
            for k in range(npl):
                tot += tabs[k][0][D[k]]
            if lo is None or tot < lo:
                lo = tot
            if tot != val:
                continue
            for combo in itertools.product(*[tabs[k][1][D[k]] for k in range(npl)]):
                m3 = 0
                for k, m in enumerate(combo):
                    m3 |= m << (n * k)
                if _pc(m3) != val:
                    raise AssertionError("placement size mismatch")
                out.add(m3)
        if lo != val:
            raise AssertionError("enumeration optimum %r differs from the leaf value %r" % (lo, val))
        return out

    def leaf(self):
        self.leaves += 1
        masks = [self.base0] + list(self.occ)
        val = self.place(masks)
        self.hist[val] = self.hist.get(val, 0) + 1
        if self.leaf_min is None or val < self.leaf_min:
            self.leaf_min = val
        if val < self.T:
            self.below += 1
            self.sets |= self.optimal_sets(masks, val)

    def run(self):
        rec = self.go()
        rec.pop("solutions", None)
        rec["hist"] = {str(k): v for k, v in sorted(self.hist.items())}
        rec["leaves_below_T"] = self.below
        rec["sets_found"] = len(self.sets)
        return rec


def initial_todo(q, rmax):
    P = indep.Plane(q)
    G = P.group()
    todo = []
    for r in range(1, rmax + 1):
        for S0, size in indep.orbit_reps(P, r, G):
            todo.append({"r": r, "S0": S0, "orbit_size": size, "prefix": []})
    return todo, len(G)


def enumerate_all(q, T, rmax):
    """Small cases (controls): every set below T, over all orbit representatives."""
    P = indep.Plane(q)
    todo, _g = initial_todo(q, rmax)
    sets = set()
    recs = []
    for it in todo:
        s = EnumSearch(P, it["S0"], T)
        recs.append(s.run())
        sets |= s.sets
    return sets, recs


def paths(out_dir, q=4, T=29):
    return (os.path.join(out_dir, "enum-q%d-T%d.json" % (q, T)),
            os.path.join(out_dir, "sets-q%d-T%d.json" % (q, T)))


def load_sets(out_dir, q=4, T=29):
    _p, spath = paths(out_dir, q, T)
    if not os.path.exists(spath):
        return set()
    with open(spath) as fh:
        return set(int(h, 16) for h in json.load(fh)["sets"])


def _dump(obj, path, indent=None):
    with open(path + ".tmp", "w") as fh:
        json.dump(obj, fh, indent=indent)
    os.replace(path + ".tmp", path)


def queue(out_dir, budget, label, item_cap=300.0, q=4, T=29):
    """Resumable: out_dir/enum-q4-T29.json (progress) and out_dir/sets-q4-T29.json (every
    distinct set found by finished items). Sets of an item are added only when the item finishes,
    and the sets file is written before the progress file, so a cut never loses or half-adds."""
    os.makedirs(out_dir, exist_ok=True)
    path, spath = paths(out_dir, q, T)
    P = indep.Plane(q)
    if os.path.exists(path):
        with open(path) as fh:
            st = json.load(fh)
    else:
        todo, gorder = initial_todo(q, RMAX[q])
        st = {"q": q, "T": T, "rmax": RMAX[q], "group_order": gorder, "made_with": MADE_WITH,
              "encoding": "a set is a 64-bit mask, bit 16 z + 4 x + y for the point (x, y, z); "
                          "F_4 coded 0, 1, a = 2, a + 1 = 3 with a^2 = a + 1",
              "todo": todo, "finished": [], "sessions": []}
    sets = load_sets(out_dir, q, T)
    t0 = time.time()
    sess = {"label": label, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "finished_items": 0, "splits": 0}
    st["sessions"].append(sess)

    def save(with_sets):
        sess["seconds"] = round(time.time() - t0, 1)
        st["complete"] = not st["todo"]
        st["n_sets"] = len(sets)
        lm = [x["leaf_min"] for x in st["finished"] if x["leaf_min"] is not None]
        st["leaf_min"] = min(lm) if lm else None
        tot = {}
        for x in st["finished"]:
            for k, v in x["hist"].items():
                tot[k] = tot.get(k, 0) + v
        st["leaf_values"] = {k: tot[k] for k in sorted(tot, key=int)}
        st["nodes"] = sum(x["nodes"] for x in st["finished"])
        if with_sets:
            _dump({"q": q, "T": T, "made_with": MADE_WITH, "encoding": st["encoding"],
                   "count": len(sets), "sets": ["%016x" % m for m in sorted(sets)]}, spath)
        _dump(st, path, indent=1)

    while st["todo"]:
        left = t0 + budget - time.time()
        if left < 5:
            break
        it = st["todo"][0]
        cap = min(item_cap, left)
        s = EnumSearch(P, it["S0"], T, prefix=it["prefix"], deadline=time.time() + cap)
        a = time.time()
        try:
            rec = s.run()
        except indep.OutOfTime:
            if cap >= item_cap - 1e-6:
                st["todo"] = [dict(it, prefix=it["prefix"] + [i]) for i in range(it["r"])] + st["todo"][1:]
                sess["splits"] += 1
                save(False)
                continue
            break
        rec["seconds"] = round(time.time() - a, 2)
        rec["orbit_size"] = it["orbit_size"]
        new = s.sets - sets
        rec["new_sets"] = len(new)
        sets |= new
        st["finished"].append(rec)
        st["todo"].pop(0)
        sess["finished_items"] += 1
        save(True)
    save(True)
    return st
