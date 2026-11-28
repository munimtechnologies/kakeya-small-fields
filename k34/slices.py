# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Exact search for small Kakeya sets in F_q^3 by slicing along a smallest plane (see PROOF.md).

Setting.  Let K be a Kakeya set in F_q^3 with |K| <= T - 1 that is a union of one line per
direction (every inclusion-minimal Kakeya set is).  Let P_0 be a plane with the fewest points of K
among all q^3 + q^2 + q planes and move it to z = 0 by an affine map.  The planes z = c (c in
F_q) cut K into slices K_c with |K_c| >= |K_0| = m, so q*m <= |K| and m <= (T - 1) // q.

The chosen line of direction (u, 1), u in F_q^2, is {(f(u) + t u, t)}.  In plane z = c it gives
the point f(u) + c u, so K_c contains S_c = {f(u) + c u : u in F_q^2}; S_0 is the image of f,
r = |S_0| <= m.  The q + 1 remaining ("horizontal") directions (d, 0) have their lines inside
single planes z = c.  Hence

    |K| = sum_c |S_c  union  H_c|,         H_c = horizontal lines placed in plane c,

and, because |K_c| >= m >= r for every c,

    |K| >= r + sum_{c != 0} max(|S_c|, r).                                         (*)

Symmetry: the affine (and, for q = 4, Frobenius) maps fixing z = 0 act on plane 0 as AGL(2, q)
(times Frobenius), so S_0 may be taken as an orbit representative; the shear
(x, y, z) -> ((x, y) + z beta, z) fixes every plane z = c and plane 0 pointwise and turns f into
u -> f(u - beta), so f(0) may be taken to be any fixed point of S_0 (here S_0[0]).

Search: for every r <= (T - 1) // q and every orbit representative S_0 of size r, a depth-first
search assigns f(u) in S_0 direction by direction (surjective onto S_0), pruning when the bound
(*) - strengthened by the points that unassigned directions are forced to add - reaches T.  At
each leaf the horizontal lines are placed optimally (exact minimum over all placements), giving
the exact smallest |K| for that f.  A leaf below T is an explicit Kakeya set below T.

If every subproblem completes and no leaf is below T, then every Kakeya set in F_q^3 has at
least T points."""
import itertools
import json
import os
import time

# ------------------------------------------------------------------ fields


def field(q):
    """Addition and multiplication tables of F_q (q prime <= 7, or q = 4 coded 0, 1, a, a+1 as
    0, 1, 2, 3 with a^2 = a + 1), the Frobenius map, and a generator of the multiplicative
    group."""
    if q == 4:
        def mul(x, y):
            r = 0
            for k in range(2):
                if (y >> k) & 1:
                    r ^= x << k
            if r & 4:
                r ^= 0b111
            return r
        add = [[x ^ y for y in range(4)] for x in range(4)]
        mult = [[mul(x, y) for y in range(4)] for x in range(4)]
        frob = [mult[x][x] for x in range(4)]
        gen = 2
    elif q in (2, 3, 5, 7):
        add = [[(x + y) % q for y in range(q)] for x in range(q)]
        mult = [[(x * y) % q for y in range(q)] for x in range(q)]
        frob = list(range(q))
        gen = {2: 1, 3: 2, 5: 2, 7: 3}[q]
    else:
        raise ValueError("q must be 2, 3, 4, 5 or 7")
    return add, mult, frob, gen


class Geo:
    """The affine plane F_q^2 (points p = x * q + y) with its horizontal line pencils."""

    def __init__(self, q):
        add, mul, frob, gen = field(q)
        self.q = q
        self.Q = Q = q * q
        self.add1, self.mul1, self.frob1, self.gen = add, mul, frob, gen
        self.xy = [(p // q, p % q) for p in range(Q)]
        self.padd = [[self.idx(add[a // q][b // q], add[a % q][b % q]) for b in range(Q)]
                     for a in range(Q)]
        self.psmul = [[self.idx(mul[l][p // q], mul[l][p % q]) for p in range(Q)]
                      for l in range(q)]
        # directions of the plane: (0, 1) and (1, l)
        self.hdirs = [self.idx(0, 1)] + [self.idx(1, l) for l in range(q)]
        self.hlines = []
        for d in self.hdirs:
            seen = []
            for p in range(Q):
                m = 0
                for t in range(q):
                    m |= 1 << self.padd[p][self.psmul[t][d]]
                if m not in seen:
                    seen.append(m)
            if len(seen) != q:
                raise AssertionError("parallel class of wrong size")
            self.hlines.append(seen)
        self.nz = list(range(1, q))

    def idx(self, x, y):
        return x * self.q + y

    def generators(self):
        """Permutations of the plane points generating AGL(2, q) (times Frobenius for q = 4)."""
        q, add, mul = self.q, self.add1, self.mul1
        idx = self.idx
        gens = []
        trans = [(1, 0), (0, 1)] + ([(2, 0), (0, 2)] if q == 4 else [])
        for tx, ty in trans:
            gens.append(tuple(idx(add[x][tx], add[y][ty]) for x, y in self.xy))
        for l in ([1, 2] if q == 4 else [1]):
            gens.append(tuple(idx(add[x][mul[l][y]], y) for x, y in self.xy))
        gens.append(tuple(idx(y, x) for x, y in self.xy))
        if q > 2:
            gens.append(tuple(idx(mul[self.gen][x], y) for x, y in self.xy))
        if q == 4:
            gens.append(tuple(idx(self.frob1[x], self.frob1[y]) for x, y in self.xy))
        return gens


def group_order(geo):
    """Order of the permutation group generated by geo.generators() (closure by BFS)."""
    gens = geo.generators()
    ident = tuple(range(geo.Q))
    seen = {ident}
    todo = [ident]
    while todo:
        g = todo.pop()
        for h in gens:
            gh = tuple(h[g[p]] for p in range(geo.Q))
            if gh not in seen:
                seen.add(gh)
                todo.append(gh)
    return len(seen)


def orbits(geo, r):
    """Orbit representatives (lexicographically smallest member) and orbit sizes of the r-subsets
    of the plane under the group generated by geo.generators()."""
    gens = geo.generators()
    seen = set()
    out = []
    for S in itertools.combinations(range(geo.Q), r):
        if S in seen:
            continue
        orb = {S}
        todo = [S]
        while todo:
            A = todo.pop()
            for g in gens:
                B = tuple(sorted(g[p] for p in A))
                if B not in orb:
                    orb.add(B)
                    todo.append(B)
        seen |= orb
        out.append((S, len(orb)))
    return out


# ------------------------------------------------------------------ search


class Timeout(Exception):
    pass


class Found(Exception):
    pass


if hasattr(int, "bit_count"):
    def popcount(m):
        return m.bit_count()
else:  # pragma: no cover
    def popcount(m):
        return bin(m).count("1")


class SliceSearch:
    """Depth-first search over f: F_q^2 -> S0 (surjective, f(0) = S0[0]) for one S0."""

    def __init__(self, geo, S0, T, prefix=(), deadline=None, stop_at_first=False,
                 max_solutions=5):
        self.g = geo
        Q = geo.Q
        self.S0 = list(S0)
        self.r = r = len(S0)
        self.T = T
        self.prefix = list(prefix)
        self.deadline = deadline
        self.stop = stop_at_first
        self.max_solutions = max_solutions
        self.nz = geo.nz
        self.nc = nc = len(self.nz)
        self.PT = [[[geo.padd[self.S0[i]][geo.psmul[c][u]] for i in range(r)] for u in range(Q)]
                   for c in self.nz]
        self.MASK = []
        for ci in range(nc):
            row = []
            for u in range(Q):
                m = 0
                for p in self.PT[ci][u]:
                    m |= 1 << p
                row.append(m)
            self.MASK.append(row)
        self.f = [-1] * Q
        self.cnt = [[0] * Q for _ in range(nc)]
        self.occ = [0] * nc
        self.s = [0] * nc
        self.used = [0] * r
        self.nunused = r
        self.B0 = 0
        for p in self.S0:
            self.B0 |= 1 << p
        self.nodes = 0
        self.pruned = 0
        self.leaves = 0
        self.leaf_min = None
        self.hist = {}
        self.solutions = []
        self.cost_cache = {}

    # -------------------------------------------------------------- state updates
    def _assign(self, u, i):
        self.f[u] = i
        if self.used[i] == 0:
            self.nunused -= 1
        self.used[i] += 1
        for ci in range(self.nc):
            p = self.PT[ci][u][i]
            c = self.cnt[ci]
            if c[p] == 0:
                self.occ[ci] |= 1 << p
                self.s[ci] += 1
            c[p] += 1

    def _unassign(self, u, i):
        self.f[u] = -1
        self.used[i] -= 1
        if self.used[i] == 0:
            self.nunused += 1
        for ci in range(self.nc):
            p = self.PT[ci][u][i]
            c = self.cnt[ci]
            c[p] -= 1
            if c[p] == 0:
                self.occ[ci] &= ~(1 << p)
                self.s[ci] -= 1

    # -------------------------------------------------------------- search
    def run(self):
        """Returns a record; raises Timeout if the deadline passes."""
        t0 = time.time()
        self._assign(0, 0)
        try:
            self._dfs(1, 0)
        except Found:
            pass
        rec = {"r": self.r, "S0": self.S0, "prefix": self.prefix, "T": self.T,
               "nodes": self.nodes, "pruned": self.pruned, "leaves": self.leaves,
               "leaf_min": self.leaf_min,
               "hist": {str(k): v for k, v in sorted(self.hist.items())},
               "solutions": self.solutions, "seconds": round(time.time() - t0, 2),
               "complete": True}
        return rec

    def _dfs(self, nass, level):
        self.nodes += 1
        if self.deadline is not None and (self.nodes & 2047) == 0 and time.time() > self.deadline:
            raise Timeout()
        Q = self.g.Q
        r = self.r
        if nass == Q:
            if self.nunused == 0:
                self._leaf()
            return
        if self.nunused > Q - nass:
            return
        occ, PT, MASK, nc, f = self.occ, self.PT, self.MASK, self.nc, self.f
        N = [0] * nc
        best_u, best_key = -1, -1
        for u in range(Q):
            if f[u] >= 0:
                continue
            for ci in range(nc):
                if not (occ[ci] & MASK[ci][u]):
                    N[ci] += 1
            mn = nc + 1
            for i in range(r):
                a = 0
                for ci in range(nc):
                    if not ((occ[ci] >> PT[ci][u][i]) & 1):
                        a += 1
                if a < mn:
                    mn = a
                    if mn == 0:
                        break
            if mn > best_key:
                best_key, best_u = mn, u
        lb = r
        s = self.s
        for ci in range(nc):
            v = s[ci] + (N[ci] + r - 1) // r
            lb += v if v > r else r
        if lb >= self.T:
            self.pruned += 1
            return
        u = best_u
        choices = [self.prefix[level]] if level < len(self.prefix) else range(r)
        T = self.T
        for i in choices:
            self._assign(u, i)
            lb2 = r
            for x in s:
                lb2 += x if x > r else r
            if lb2 < T:
                self._dfs(nass + 1, level + 1)
            self._unassign(u, i)

    # -------------------------------------------------------------- leaves
    def plane_costs(self, B):
        """cost[D] = fewest points of (B union one line of each direction in D) in one plane."""
        c = self.cost_cache.get(B)
        if c is not None:
            return c
        if len(self.cost_cache) > 200000:
            self.cost_cache.clear()
        HL = self.g.hlines
        nd = len(HL)
        q = self.g.q
        cost = [0] * (1 << nd)
        for D in range(1 << nd):
            dl = [d for d in range(nd) if (D >> d) & 1]
            best = None
            for ch in itertools.product(range(q), repeat=len(dl)):
                m = B
                for d, j in zip(dl, ch):
                    m |= HL[d][j]
                v = popcount(m)
                if best is None or v < best:
                    best = v
            cost[D] = best
        self.cost_cache[B] = cost
        return cost

    def assign_min(self, costs):
        """Exact minimum over placements of each horizontal direction in one plane."""
        nd = len(self.g.hlines)
        full = (1 << nd) - 1
        g = list(costs[0])
        for cost in costs[1:]:
            ng = [0] * (full + 1)
            for D in range(full + 1):
                best = None
                E = D
                while True:
                    v = g[D ^ E] + cost[E]
                    if best is None or v < best:
                        best = v
                    if E == 0:
                        break
                    E = (E - 1) & D
                ng[D] = best
            g = ng
        return g[full]

    def masks(self):
        return [self.B0] + list(self.occ)

    def _leaf(self):
        self.leaves += 1
        masks = self.masks()
        costs = [self.plane_costs(m) for m in masks]
        total = self.assign_min(costs)
        self.hist[total] = self.hist.get(total, 0) + 1
        if self.leaf_min is None or total < self.leaf_min:
            self.leaf_min = total
        if total < self.T:
            if len(self.solutions) < self.max_solutions:
                pts = self.realize()
                self.solutions.append({"size": total, "points": pts,
                                       "f": [self.S0[i] for i in self.f]})
            if self.stop:
                raise Found()

    def realize(self):
        """An explicit Kakeya set for the current f with the optimal horizontal lines, as a sorted
        list of [x, y, z]."""
        geo = self.g
        q = geo.q
        HL = geo.hlines
        nd = len(HL)
        planes = [0] + list(self.nz)
        masks = self.masks()
        best = None
        for assign in itertools.product(range(q), repeat=nd):
            # assign[d] = index into planes of the plane holding direction d
            tot = 0
            choice = []
            for k in range(q):
                dl = [d for d in range(nd) if assign[d] == k]
                bm, bch = None, None
                for ch in itertools.product(range(q), repeat=len(dl)):
                    m = masks[k]
                    for d, j in zip(dl, ch):
                        m |= HL[d][j]
                    if bm is None or popcount(m) < popcount(bm):
                        bm, bch = m, ch
                tot += popcount(bm)
                choice.append((dl, bch))
            if best is None or tot < best[0]:
                best = (tot, choice)
        pts = set()
        for u in range(geo.Q):
            base = self.S0[self.f[u]]
            for t in range(q):
                x, y = geo.xy[geo.padd[base][geo.psmul[t][u]]]
                pts.add((x, y, t))
        for k, (dl, ch) in enumerate(best[1]):
            c = planes[k]
            for d, j in zip(dl, ch):
                for p in range(geo.Q):
                    if (HL[d][j] >> p) & 1:
                        x, y = geo.xy[p]
                        pts.add((x, y, c))
        out = sorted(list(p) for p in pts)
        if len(out) != best[0]:
            raise AssertionError("realised set has %d points, expected %d" % (len(out), best[0]))
        return out


def leaf_value(geo, fvals):
    """Exact smallest |K| for a given f (list of plane points, index u), with S0 = image of f.
    Used by the controls."""
    S0 = sorted(set(fvals))
    s = SliceSearch(geo, S0, T=10 ** 9)
    for u, v in enumerate(fvals):
        s._assign(u, S0.index(v))
    costs = [s.plane_costs(m) for m in s.masks()]
    return s.assign_min(costs), s


# ------------------------------------------------------------------ queue across gate entries


def initial_items(geo, T):
    rmax = (T - 1) // geo.q
    items = []
    for r in range(1, rmax + 1):
        for rep, size in orbits(geo, r):
            items.append({"r": r, "S0": list(rep), "orbit_size": size, "prefix": []})
    return items


def covered(prefixes, r, pre=()):
    """True if the set of branch prefixes covers the whole search tree."""
    prefixes = set(tuple(p) for p in prefixes)
    depth = max((len(p) for p in prefixes), default=0)

    def rec(pre):
        if pre in prefixes:
            return True
        if len(pre) >= depth:
            return False
        return all(rec(pre + (i,)) for i in range(r))
    return rec(tuple(pre))


def run_queue(q, T, out_dir, budget, label, item_cap=150.0, log=print):
    """Continue the queued search for (q, T): load progress, run items until the budget is spent,
    split items that hit item_cap into their r children, save progress after every item."""
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, "progress-q%d-T%d.json" % (q, T))
    geo = Geo(q)
    if os.path.exists(path):
        with open(path) as fh:
            prog = json.load(fh)
    else:
        items = initial_items(geo, T)
        prog = {"q": q, "T": T,
                "made_with": "AI agents working in MV2's name; not checked by a human mathematician",
                "orbit_counts": {}, "pending": items, "done": [], "entries": []}
        for it in items:
            k = str(it["r"])
            prog["orbit_counts"][k] = prog["orbit_counts"].get(k, 0) + 1
    t_start = time.time()
    t_end = t_start + budget
    entry = {"label": label, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
             "items_done": 0, "splits": 0, "nodes": 0}

    def save():
        entry["seconds"] = round(time.time() - t_start, 1)
        prog["complete"] = not prog["pending"]
        prog["solutions_found"] = sum(len(d["solutions"]) for d in prog["done"])
        mins = [d["leaf_min"] for d in prog["done"] if d["leaf_min"] is not None]
        prog["leaf_min_overall"] = min(mins) if mins else None
        tmp = path + ".tmp"
        with open(tmp, "w") as fh:
            json.dump(prog, fh, indent=1)
        os.replace(tmp, path)

    prog["entries"].append(entry)
    while prog["pending"]:
        left = t_end - time.time()
        if left < 5:
            break
        it = prog["pending"][0]
        cap = min(item_cap, left)
        s = SliceSearch(geo, it["S0"], T, prefix=it["prefix"], deadline=time.time() + cap)
        try:
            rec = s.run()
        except Timeout:
            entry["nodes"] += s.nodes
            if cap >= item_cap - 1e-6:
                kids = [{"r": it["r"], "S0": it["S0"], "orbit_size": it["orbit_size"],
                         "prefix": it["prefix"] + [i]} for i in range(it["r"])]
                prog["pending"] = kids + prog["pending"][1:]
                entry["splits"] += 1
                log("split r=%d S0=%s prefix=%s after %d nodes" % (
                    it["r"], it["S0"], it["prefix"], s.nodes))
                save()
                continue
            log("entry budget spent inside r=%d S0=%s prefix=%s" % (it["r"], it["S0"], it["prefix"]))
            break
        rec["orbit_size"] = it["orbit_size"]
        prog["done"].append(rec)
        prog["pending"].pop(0)
        entry["items_done"] += 1
        entry["nodes"] += rec["nodes"]
        log("done r=%d S0=%s prefix=%s nodes=%d leaves=%d leaf_min=%s sol=%d %.1fs" % (
            rec["r"], rec["S0"], rec["prefix"], rec["nodes"], rec["leaves"], rec["leaf_min"],
            len(rec["solutions"]), rec["seconds"]))
        save()
    save()
    return prog


def full_search(q, T, stop_at_first=False):
    """Whole search in one call (small cases, e.g. the q = 3 controls)."""
    geo = Geo(q)
    out = []
    for it in initial_items(geo, T):
        s = SliceSearch(geo, it["S0"], T, stop_at_first=stop_at_first)
        rec = s.run()
        rec["orbit_size"] = it["orbit_size"]
        out.append(rec)
    return out
