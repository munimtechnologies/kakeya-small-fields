# SPDX-License-Identifier: Apache-2.0
# Copyright 2026 MV2 of Munim, Inc. (mv2@munimtech.com)
# Made with AI agents working in MV2's name. Not yet checked by a human mathematician.
"""Second, independently written search for small Kakeya sets in F_q^3 (q = 3, 4).

It re-implements the hand reduction of k34/PROOF.md from scratch and shares no code with
k34/slices.py or k34/verify.py:

* fields from logarithm tables, the plane's affine group (times Frobenius for q = 4) built by
  listing every invertible matrix and translation (not from generators), orbits by applying
  the whole group;
* a depth-first search over f: F_q^2 -> S_0 (surjective, f(0) = S_0[0] by the shear), with the
  bound |K| >= r + sum_{c != 0} max(|S_c| + ceil(N_c / r), r), where N_c counts unassigned
  directions all of whose candidate points in plane c are still new;
* leaves: exact optimal placement of the q + 1 horizontal directions by a subset dynamic program
  over planes, written here from scratch;
* its own Kakeya checker over normalised directions.

A leaf below T is realised as an explicit point set and checked."""
import itertools
import json
import os
import time

# ------------------------------------------------------------------ field and plane


def field_tables(q):
    if q == 4:
        exp = [1, 2, 3]
        log = {1: 0, 2: 1, 3: 2}

        def mul(x, y):
            return 0 if x == 0 or y == 0 else exp[(log[x] + log[y]) % 3]

        add = [[x ^ y for y in range(4)] for x in range(4)]
        mult = [[mul(x, y) for y in range(4)] for x in range(4)]
        neg = [0, 1, 2, 3]
        frob = [mult[x][x] for x in range(4)]
    elif q == 3:
        add = [[(x + y) % 3 for y in range(3)] for x in range(3)]
        mult = [[(x * y) % 3 for y in range(3)] for x in range(3)]
        neg = [0, 2, 1]
        frob = [0, 1, 2]
    else:
        raise ValueError("q must be 3 or 4")
    return add, mult, neg, frob


class Plane:
    def __init__(self, q):
        self.q = q
        self.n = q * q
        A, M, N, F = field_tables(q)
        self.A, self.M, self.N, self.F = A, M, N, F
        self.pt = [(x, y) for x in range(q) for y in range(q)]
        self.ix = {p: k for k, p in enumerate(self.pt)}
        self.vadd = [[self.ix[(A[a[0]][b[0]], A[a[1]][b[1]])] for b in self.pt] for a in self.pt]
        self.smul = [[self.ix[(M[c][a[0]], M[c][a[1]])] for a in self.pt] for c in range(q)]
        self.hdirs = [(0, 1)] + [(1, l) for l in range(q)]
        self.hlines = []
        for d in self.hdirs:
            di = self.ix[d]
            lines = set()
            for p in range(self.n):
                m = 0
                for t in range(q):
                    m |= 1 << self.vadd[p][self.smul[t][di]]
                lines.add(m)
            if len(lines) != q:
                raise AssertionError("bad parallel class")
            self.hlines.append(sorted(lines))

    def group(self):
        """Every map p -> M (phi(p)) + t with M invertible, t a translation and phi the identity or
        (for q = 4) Frobenius, as a tuple permutation of point indices."""
        q, A, M, N, F = self.q, self.A, self.M, self.N, self.F
        phis = [list(range(q))] + ([F] if q == 4 else [])
        out = set()
        for a, b, c, d in itertools.product(range(q), repeat=4):
            if A[M[a][d]][N[M[b][c]]] == 0:
                continue
            for tx, ty in itertools.product(range(q), repeat=2):
                for ph in phis:
                    perm = []
                    for x, y in self.pt:
                        x2, y2 = ph[x], ph[y]
                        perm.append(self.ix[(A[A[M[a][x2]][M[b][y2]]][tx],
                                             A[A[M[c][x2]][M[d][y2]]][ty])])
                    out.add(tuple(perm))
        return sorted(out)


def orbit_reps(P, r, G=None):
    G = G if G is not None else P.group()
    seen = set()
    reps = []
    for S in itertools.combinations(range(P.n), r):
        if S in seen:
            continue
        orb = set(tuple(sorted(g[p] for p in S)) for g in G)
        seen |= orb
        reps.append((list(S), len(orb)))
    return reps


# ------------------------------------------------------------------ Kakeya checker


def kakeya_ok(points, q):
    """Own checker: every normalised direction of F_q^3 has a full line inside the set."""
    A, M, _N, _F = field_tables(q)
    S = set(tuple(p) for p in points)
    dirs = [(1, a, b) for a in range(q) for b in range(q)] + [(0, 1, b) for b in range(q)] + [(0, 0, 1)]
    for d in dirs:
        if not any(all((A[p[0]][M[t][d[0]]], A[p[1]][M[t][d[1]]], A[p[2]][M[t][d[2]]]) in S
                       for t in range(q)) for p in S):
            return False
    return True


def kss_q4():
    """Kopparty-Saraf-Sudan: plane z = 0 plus (b z + b^2, c z + c^2, z), z != 0."""
    A, M, _N, _F = field_tables(4)
    pts = {(x, y, 0) for x in range(4) for y in range(4)}
    for b in range(4):
        for c in range(4):
            for z in range(1, 4):
                pts.add((A[M[b][z]][M[b][b]], A[M[c][z]][M[c][c]], z))
    return sorted(pts)


# ------------------------------------------------------------------ search


class OutOfTime(Exception):
    pass


class Stop(Exception):
    pass


def _pc(m):
    return bin(m).count("1")


class Search:
    def __init__(self, P, S0, T, prefix=(), deadline=None, stop_first=False, keep=3):
        self.P = P
        q, n = P.q, P.n
        self.S0 = list(S0)
        self.r = r = len(S0)
        self.T = T
        self.prefix = list(prefix)
        self.deadline = deadline
        self.stop_first = stop_first
        self.keep = keep
        self.cs = list(range(1, q))
        k = len(self.cs)
        # bit[u][i][j]: bit of the point S0[i] + c_j u in plane c_j
        self.bit = [[[1 << P.vadd[self.S0[i]][P.smul[c][u]] for c in self.cs] for i in range(r)]
                    for u in range(n)]
        # um[u][j]: all candidate points of direction u in plane c_j
        self.um = [[0] * k for _ in range(n)]
        for u in range(n):
            for i in range(r):
                for j in range(k):
                    self.um[u][j] |= self.bit[u][i][j]
        self.cnt = [dict() for _ in range(k)]
        self.occ = [0] * k
        self.f = [None] * n
        self.used = [0] * r
        self.unused = r
        self.nodes = self.leaves = self.pruned = 0
        self.leaf_min = None
        self.found = []
        self.cache = {}
        self.base0 = 0
        for p in self.S0:
            self.base0 |= 1 << p

    def put(self, u, i):
        self.f[u] = i
        if self.used[i] == 0:
            self.unused -= 1
        self.used[i] += 1
        for j, b in enumerate(self.bit[u][i]):
            c = self.cnt[j].get(b, 0)
            if c == 0:
                self.occ[j] |= b
            self.cnt[j][b] = c + 1

    def take(self, u, i):
        self.f[u] = None
        self.used[i] -= 1
        if self.used[i] == 0:
            self.unused += 1
        for j, b in enumerate(self.bit[u][i]):
            c = self.cnt[j][b] - 1
            self.cnt[j][b] = c
            if c == 0:
                self.occ[j] &= ~b

    def bound(self, extra):
        r = self.r
        tot = r
        for j, o in enumerate(self.occ):
            v = _pc(o) + extra[j]
            tot += v if v > r else r
        return tot

    def go(self):
        self.put(0, 0)
        try:
            self.dfs(0, self.P.n - 1)
        except Stop:
            pass
        return {"r": self.r, "S0": self.S0, "prefix": self.prefix, "T": self.T,
                "nodes": self.nodes, "pruned": self.pruned, "leaves": self.leaves,
                "leaf_min": self.leaf_min, "solutions": self.found, "complete": True}

    def dfs(self, depth, left):
        self.nodes += 1
        if self.deadline is not None and self.nodes % 4096 == 0 and time.time() > self.deadline:
            raise OutOfTime()
        if left == 0:
            if self.unused == 0:
                self.leaf()
            return
        if self.unused > left:
            return
        r = self.r
        k = len(self.cs)
        allnew = [0] * k
        pick, pick_key = None, None
        for u in range(self.P.n):
            if self.f[u] is not None:
                continue
            bu = self.bit[u]
            occ = self.occ
            umu = self.um[u]
            for j in range(k):
                if not (umu[j] & occ[j]):
                    allnew[j] += 1
            news = []
            for i in range(r):
                bi = bu[i]
                s = 0
                for j in range(k):
                    if not (bi[j] & occ[j]):
                        s += 1
                news.append(s)
            key = (min(news), sum(news))
            if pick_key is None or key > pick_key:
                pick, pick_key = u, key
        extra = [(a + r - 1) // r for a in allnew]
        if self.bound(extra) >= self.T:
            self.pruned += 1
            return
        if depth < len(self.prefix):
            choices = [self.prefix[depth]]
        else:
            choices = range(r)
        zero = [0] * k
        for i in choices:
            self.put(pick, i)
            if self.bound(zero) < self.T:
                self.dfs(depth + 1, left - 1)
            self.take(pick, i)

    # leaves -----------------------------------------------------------------
    def costs(self, mask):
        """cost[D]: fewest points of mask plus one line of each horizontal direction in D."""
        c = self.cache.get(mask)
        if c is not None:
            return c
        if len(self.cache) > 300000:
            self.cache.clear()
        HL = self.P.hlines
        nd = len(HL)
        best = [None] * (1 << nd)
        # build cost[D] by extending smaller subsets: keep every union reachable (sets of masks)
        reach = {0: {mask}}
        best[0] = _pc(mask)
        for D in range(1, 1 << nd):
            low = (D & -D).bit_length() - 1
            prev = reach[D & ~(1 << low)]
            cur = set()
            for m in prev:
                for line in HL[low]:
                    cur.add(m | line)
            reach[D] = cur
            best[D] = min(_pc(m) for m in cur)
        self.cache[mask] = best
        return best

    def place(self, masks):
        nd = len(self.P.hlines)
        full = (1 << nd) - 1
        g = None
        for mask in masks:
            c = self.costs(mask)
            if g is None:
                g = list(c)
                continue
            ng = []
            for D in range(full + 1):
                v = None
                sub = D
                while True:
                    w = g[sub] + c[D & ~sub]
                    if v is None or w < v:
                        v = w
                    if sub == 0:
                        break
                    sub = (sub - 1) & D
                ng.append(v)
            g = ng
        return g[full]

    def leaf(self):
        self.leaves += 1
        masks = [self.base0] + list(self.occ)
        val = self.place(masks)
        if self.leaf_min is None or val < self.leaf_min:
            self.leaf_min = val
        if val < self.T:
            if len(self.found) < self.keep:
                pts = self.realise(masks)
                self.found.append({"value": val, "size": len(pts), "points": pts,
                                   "f": [self.S0[i] for i in self.f]})
            if self.stop_first:
                raise Stop()

    def realise(self, masks):
        """Brute force: best plane and line for every horizontal direction."""
        P = self.P
        q = P.q
        HL = P.hlines
        best = None
        for planes in itertools.product(range(q), repeat=len(HL)):
            for lines in itertools.product(range(q), repeat=len(HL)):
                ms = list(masks)
                for d in range(len(HL)):
                    ms[planes[d]] |= HL[d][lines[d]]
                v = sum(_pc(m) for m in ms)
                if best is None or v < best[0]:
                    best = (v, ms)
        pts = set()
        zs = [0] + self.cs
        for k, m in enumerate(best[1]):
            for p in range(P.n):
                if (m >> p) & 1:
                    pts.add((P.pt[p][0], P.pt[p][1], zs[k]))
        # transversal lines, rebuilt from f
        for u in range(P.n):
            for t in range(q):
                p = P.vadd[self.S0[self.f[u]]][P.smul[t][u]]
                if (P.pt[p][0], P.pt[p][1], t) not in pts:
                    raise AssertionError("transversal point missing")
        return sorted(list(p) for p in pts)


# ------------------------------------------------------------------ whole searches


def search_all(q, T, stop_first=False):
    P = Plane(q)
    G = P.group()
    out = []
    for r in range(1, (T - 1) // q + 1):
        for S0, size in orbit_reps(P, r, G):
            rec = Search(P, S0, T, stop_first=stop_first).go()
            rec["orbit_size"] = size
            out.append(rec)
    return out


def tree_covered(prefixes, r):
    pre = set(tuple(p) for p in prefixes)
    if not pre:
        return False
    depth = max(len(p) for p in pre)

    def ok(p):
        if p in pre:
            return True
        if len(p) >= depth:
            return False
        return all(ok(p + (i,)) for i in range(r))
    return ok(())


def queue(q, T, out_dir, budget, label, item_cap=280.0):
    """Resumable queue, own file format: out_dir/indep-q{q}-T{T}.json."""
    os.makedirs(out_dir, exist_ok=True)
    path = os.path.join(out_dir, "indep-q%d-T%d.json" % (q, T))
    P = Plane(q)
    if os.path.exists(path):
        with open(path) as fh:
            st = json.load(fh)
    else:
        G = P.group()
        todo = []
        for r in range(1, (T - 1) // q + 1):
            for S0, size in orbit_reps(P, r, G):
                todo.append({"r": r, "S0": S0, "orbit_size": size, "prefix": []})
        st = {"q": q, "T": T, "group_order": len(G),
              "made_with": "AI agents working in MV2's name; not checked by a human mathematician",
              "todo": todo, "finished": [], "sessions": []}
    t0 = time.time()
    sess = {"label": label, "started": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
            "finished_items": 0, "splits": 0}
    st["sessions"].append(sess)

    def save():
        sess["seconds"] = round(time.time() - t0, 1)
        st["complete"] = not st["todo"]
        st["sets_below_T"] = sum(len(x["solutions"]) for x in st["finished"])
        lm = [x["leaf_min"] for x in st["finished"] if x["leaf_min"] is not None]
        st["leaf_min"] = min(lm) if lm else None
        with open(path + ".tmp", "w") as fh:
            json.dump(st, fh, indent=1)
        os.replace(path + ".tmp", path)

    while st["todo"]:
        left = t0 + budget - time.time()
        if left < 5:
            break
        it = st["todo"][0]
        cap = min(item_cap, left)
        s = Search(P, it["S0"], T, prefix=it["prefix"], deadline=time.time() + cap)
        a = time.time()
        try:
            rec = s.go()
        except OutOfTime:
            if cap >= item_cap - 1e-6:
                st["todo"] = [dict(it, prefix=it["prefix"] + [i]) for i in range(it["r"])] + st["todo"][1:]
                sess["splits"] += 1
                save()
                continue
            break
        rec["seconds"] = round(time.time() - a, 2)
        rec["orbit_size"] = it["orbit_size"]
        st["finished"].append(rec)
        st["todo"].pop(0)
        sess["finished_items"] += 1
        save()
    save()
    return st
