# sticky_h3.py -- exact unions at height 3, max-relaxation above: a proved lower bound for pi_4
# (notes a188-a190, pre-registration notes/prereg-sticky-h3.md).
#
# Setting (a188).  A full sticky tree of height k over F_3 is a sticky map P: F_3^k -> F_3^k; its
# slices are S_t = {P(d) + t d}, t = 0, 1, 2, and pi_k is the least |S_0||S_1||S_2|.  Question S7
# (is the sticky Kakeya base over F_3 below 2?) holds iff pi_k < 8^k for some k (Theorem 78).
# pi_1 = 8, pi_2 = 64, pi_3 = 512 are proved (Props 83, 84).  The max-relaxation ("game") allows
# 3971 = 11*19*19 < 4096 at height 4 (sticky-front-v1, note a190), so it cannot decide pi_4.
#
# This module makes height 3 EXACT.  A node with root map g and children T_0, T_1, T_2 has
#   S_t(T) = union over x of {g(x) + t x} x S_t(T_x),
# so children whose planes coincide in slice t contribute the UNION of their slice sets.  For a
# quadratic root (one child isolated per slice, the isolated child a bijection of t; Lemma 162),
# after relabelling the children A, B, C (A isolated in slice 0, B in 1, C in 2):
#   L = (|A0| + |B0 u C0|,  |B1| + |A1 u C1|,  |C2| + |A2 u B2|)       (exact).
# Height-2 trees are enumerated exhaustively (27^4); their slices are 9-bit masks over F_3^2.
# Affine roots at height 3 are kept relaxed (union >= max), which is still a valid lower bound.
# Only height-3 vectors that can take part in a height-4 quadratic node of product < 4096 matter
# (the down-set W, computed from the game front at height 3), so the search is restricted to W.
# Height 4 is then relaxed (union >= max) over the resulting set H3:
#   if min product >= 4096, then pi_4 = 4096 (affine roots cost >= 9 * 512 = 4608, Lemma 162),
#   and no certificate for S7 has height <= 4.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.

import itertools
import json
import random
import sys
import time

ALL_MAPS = list(itertools.product(range(3), repeat=3))
PC = [bin(m).count("1") for m in range(1 << 18)]
INF = 10 ** 9
TARGET = 4096          # 8^4
CODE = 1000000         # tree codes are < 27^4 = 531441


# ---------------------------------------------------------------- height-2 trees and their masks

def vtab():
    """V[h][t] = 3-bit mask of {h(z) + t z : z in F_3}."""
    V = []
    for h in ALL_MAPS:
        row = []
        for t in range(3):
            m = 0
            for z in range(3):
                m |= 1 << ((h[z] + t * z) % 3)
            row.append(m)
        V.append(row)
    return V


V = vtab()


def tree_masks(r, h0, h1, h2):
    """Slice masks of the height-2 tree P(d1, d2) = (r(d1), h_{d1}(d2)); point (p, q) -> bit 3p+q.
    r, h0, h1, h2 are map indices (0..26)."""
    rm = ALL_MAPS[r]
    hs = (h0, h1, h2)
    out = []
    for t in range(3):
        m = 0
        for x in range(3):
            m |= V[hs[x]][t] << (3 * ((rm[x] + t * x) % 3))
        out.append(m)
    return tuple(out)


def decode(code):
    h2 = code % 27
    code //= 27
    h1 = code % 27
    code //= 27
    h0 = code % 27
    return code // 27, h0, h1, h2


def enumerate_height2():
    """Yield (m0, m1, m2, code) for all 27^4 height-2 trees."""
    for r in range(27):
        rm = ALL_MAPS[r]
        sh = [[3 * ((rm[x] + t * x) % 3) for x in range(3)] for t in range(3)]
        for h0 in range(27):
            a = [V[h0][t] << sh[t][0] for t in range(3)]
            for h1 in range(27):
                b = [a[t] | (V[h1][t] << sh[t][1]) for t in range(3)]
                base = ((r * 27 + h0) * 27 + h1) * 27
                for h2 in range(27):
                    yield (b[0] | (V[h2][0] << sh[0][2]), b[1] | (V[h2][1] << sh[1][2]),
                           b[2] | (V[h2][2] << sh[2][2]), base + h2)


# ---------------------------------------------------------------- the affine group on F_3^2

def group_elements():
    """Lower-triangular affine maps (p, q) -> (a p + c1, b p + e q + c2), a, e != 0: 108 maps.
    Applying one of them to every slice of a tree gives the slices of another tree
    (P'(d) = M P(M^-1 d) + c), and it preserves sizes and unions."""
    return [(a, b, e, c1, c2) for a in (1, 2) for e in (1, 2)
            for b in range(3) for c1 in range(3) for c2 in range(3)]


def point_perm(g):
    a, b, e, c1, c2 = g
    perm = [0] * 9
    for p in range(3):
        for q in range(3):
            perm[3 * p + q] = 3 * ((a * p + c1) % 3) + (b * p + e * q + c2) % 3
    return perm


def mask_tables(G):
    tabs = []
    for g in G:
        perm = point_perm(g)
        tab = [0] * 512
        for m in range(512):
            o = 0
            for i in range(9):
                if m >> i & 1:
                    o |= 1 << perm[i]
            tab[m] = o
        tabs.append(tab)
    return tabs


def transformed_tree(g, r, hs):
    """The tree P'(d) = M P(M^-1 d) + c as map indices (r', h'0, h'1, h'2) (used by the tests)."""
    a, b, e, c1, c2 = g
    rm = ALL_MAPS[r]
    ainv, einv = a, e                       # in F_3, 1^-1 = 1 and 2^-1 = 2
    rnew = []
    hnew = []
    for d1 in range(3):
        x = (ainv * d1) % 3
        rnew.append((a * rm[x] + c1) % 3)
        hx = ALL_MAPS[hs[x]]
        row = []
        for d2 in range(3):
            z = (einv * (d2 - b * x)) % 3
            row.append((b * rm[x] + e * hx[z] + c2) % 3)
        hnew.append(row)
    idx = lambda f: f[0] * 9 + f[1] * 3 + f[2]
    return idx(rnew), idx(hnew[0]), idx(hnew[1]), idx(hnew[2])


# ---------------------------------------------------------------- small helpers

def leq(u, v):
    return u[0] <= v[0] and u[1] <= v[1] and u[2] <= v[2]


def minimal3(vecs):
    """Coordinatewise-minimal elements of a set of 3-vectors."""
    front = []
    for v in sorted(set(tuple(x) for x in vecs)):
        if not any(leq(f, v) for f in front):
            front.append(v)
    return front


def node_lower(root, kids):
    """Union >= max relaxation of one node (any of the 27 root maps)."""
    L = []
    for t in range(3):
        classes = {}
        for x in range(3):
            classes.setdefault((root[x] + t * x) % 3, []).append(kids[x][t])
        L.append(sum(max(v) for v in classes.values()))
    return tuple(L)


def game_front3(M2):
    R3 = set()
    for kids in itertools.product(M2, repeat=3):
        for root in ALL_MAPS:
            R3.add(node_lower(root, kids))
    return minimal3(R3)


def pareto2_insert(lst, p, q):
    for (a, b) in lst:
        if a <= p and b <= q:
            return
    lst[:] = [(a, b) for (a, b) in lst if not (p <= a and q <= b)]
    lst.append((p, q))


def reduce_submask(D):
    """D: mask -> 2-D pareto list.  Drop entries dominated by an entry at a proper submask."""
    out = {}
    for m, lst in D.items():
        keep = []
        for (p, q) in lst:
            dom = False
            s = (m - 1) & m
            while True:
                if s != m and s in D:
                    for (a, b) in D[s]:
                        if a <= p and b <= q:
                            dom = True
                            break
                if dom or s == 0:
                    break
                s = (s - 1) & m
            if not dom:
                keep.append((p, q))
        if keep:
            out[m] = keep
    return out


# ---------------------------------------------------------------- the down-set W

def w_tables(F3, top=27, target=TARGET):
    """vmax[p][v0][v1] = largest v2 (<= top) such that a child with vector v in position p
    (0 = A, 1 = B, 2 = C) of a height-4 quadratic node, with the other two children from F3,
    can give product < target; 0 if none.  W_p = {v : 1 <= v2 <= vmax[p][v0][v1]}."""
    pairs = [(X, Y) for X in F3 for Y in F3]
    lim = target - 1
    vmax = [[[0] * (top + 1) for _ in range(top + 1)] for _ in range(3)]
    for v0 in range(1, top + 1):
        for v1 in range(1, top + 1):
            b0 = b1 = b2 = 0
            for (X, Y) in pairs:
                # position A: v=A, X=B, Y=C
                l0 = v0 + (X[0] if X[0] > Y[0] else Y[0])
                l1 = X[1] + (v1 if v1 > Y[1] else Y[1])
                q = lim // (l0 * l1)
                if Y[2] + X[2] <= q:
                    c = q - Y[2]
                    if c > b0:
                        b0 = c
                # position B: X=A, v=B, Y=C
                l0 = X[0] + (v0 if v0 > Y[0] else Y[0])
                l1 = v1 + (X[1] if X[1] > Y[1] else Y[1])
                q = lim // (l0 * l1)
                if Y[2] + X[2] <= q:
                    c = q - Y[2]
                    if c > b1:
                        b1 = c
                # position C: X=A, Y=B, v=C
                l0 = X[0] + (Y[0] if Y[0] > v0 else v0)
                l1 = Y[1] + (X[1] if X[1] > v1 else v1)
                q = lim // (l0 * l1)
                c = q - (X[2] if X[2] > Y[2] else Y[2])
                if c > b2:
                    b2 = c
            vmax[0][v0][v1] = min(b0, top)
            vmax[1][v0][v1] = min(b1, top)
            vmax[2][v0][v1] = min(b2, top)
    return vmax


def make_inW(vmax, top=27):
    best = [[max(vmax[p][v0][v1] for p in range(3)) for v1 in range(top + 1)]
            for v0 in range(top + 1)]

    def inW(L):
        if L[0] < 1 or L[1] < 1 or L[0] > top or L[1] > top:
            return False
        return 1 <= L[2] <= best[L[0]][L[1]]
    return inW, best


def caps_of(best, top=27):
    c0 = c1 = c2 = 0
    for v0 in range(1, top + 1):
        for v1 in range(1, top + 1):
            if best[v0][v1] >= 1:
                c0 = max(c0, v0)
                c1 = max(c1, v1)
                c2 = max(c2, best[v0][v1])
    return (c0, c1, c2)


# ---------------------------------------------------------------- tables over height-2 trees

def build_tables(trees):
    """trees: iterable of (m0, m1, m2, code).  Returns three dicts key18 -> size*CODE + code:
    TA (A1, A2) -> min |A0|;  TB (B0, B2) -> min |B1|;  TC (C0, C1) -> min |C2|."""
    TA, TB, TC = {}, {}, {}
    for m0, m1, m2, code in trees:
        k = m1 | (m2 << 9)
        v = PC[m0] * CODE + code
        if v < TA.get(k, INF * CODE):
            TA[k] = v
        k = m0 | (m2 << 9)
        v = PC[m1] * CODE + code
        if v < TB.get(k, INF * CODE):
            TB[k] = v
        k = m0 | (m1 << 9)
        v = PC[m2] * CODE + code
        if v < TC.get(k, INF * CODE):
            TC[k] = v
    return TA, TB, TC


def inclusion_minimal(T, method="auto"):
    """Keep only entries (key, size) with no entry at a proper submask key of size <= size.
    method: "pairs" (quadratic, for small tables), "sos" (subset DP over 2^18), or "auto"."""
    if method == "pairs" or (method == "auto" and len(T) <= 2000):
        items = [(k, v // CODE) for k, v in T.items()]
        out = {}
        for k, v in T.items():
            s = v // CODE
            if not any(k2 != k and (k2 & ~k) == 0 and s2 <= s for k2, s2 in items):
                out[k] = v
        return out
    N = 1 << 18
    best = [INF] * N
    for k, v in T.items():
        s = v // CODE
        if s < best[k]:
            best[k] = s
    for i in range(18):
        bit = 1 << i
        for k in range(N):
            if k & bit:
                x = best[k ^ bit]
                if x < best[k]:
                    best[k] = x
    out = {}
    for k, v in T.items():
        s = v // CODE
        ok = True
        kk = k
        while kk:
            low = kk & -kk
            if best[k ^ low] <= s:
                ok = False
                break
            kk ^= low
        if ok:
            out[k] = v
    return out


def orbit_reps(TC, tabs):
    """One representative key per orbit of the group acting on (C0, C1) simultaneously."""
    reps = {}
    for k, v in TC.items():
        c0, c1 = k & 511, k >> 9
        canon = min(t[c0] | (t[c1] << 9) for t in tabs)
        if canon not in reps:
            reps[canon] = (k, v)
    return list(reps.values())


def exact_quadratic(TA, TB, Creps, inW, caps, tlimit=None, log=None):
    """All coordinatewise-minimal exact quadratic height-3 vectors that lie in W, with witnesses.
    Returns (dict L -> (keyA, valA, keyB, valB, keyC, valC), complete_flag, stats)."""
    cap0, cap1, cap2 = caps
    A = [(k & 511, k >> 9, v // CODE, k, v) for k, v in TA.items()]
    B = [(k & 511, k >> 9, v // CODE, k, v) for k, v in TB.items()]
    found = {}
    t0 = time.time()
    combos = 0
    done = 0
    for kc, vc in Creps:
        if tlimit is not None and time.time() - t0 > tlimit:
            return found, False, {"creps_done": done, "combos": combos}
        C0, C1, c2 = kc & 511, kc >> 9, vc // CODE
        p0, p1 = PC[C0], PC[C1]
        done += 1
        if 1 + p0 > cap0 or 1 + p1 > cap1 or c2 + 1 > cap2:
            continue
        DA = {}
        wA = {}
        for (A1, A2, a0, ka, va) in A:
            if a0 + p0 > cap0 or c2 + PC[A2] > cap2:
                continue
            x1 = PC[A1 | C1]
            if x1 + 1 > cap1:
                continue
            lst = DA.setdefault(A2, [])
            before = list(lst)
            pareto2_insert(lst, a0, x1)
            if lst != before:
                wA[(A2, a0, x1)] = (ka, va)
        DB = {}
        wB = {}
        for (B0, B2, b1, kb, vb) in B:
            if b1 + p1 > cap1 or c2 + PC[B2] > cap2:
                continue
            y0 = PC[B0 | C0]
            if y0 + 1 > cap0:
                continue
            lst = DB.setdefault(B2, [])
            before = list(lst)
            pareto2_insert(lst, y0, b1)
            if lst != before:
                wB[(B2, y0, b1)] = (kb, vb)
        DA = reduce_submask(DA)
        DB = reduce_submask(DB)
        for A2, la in DA.items():
            for B2, lb in DB.items():
                L2 = c2 + PC[A2 | B2]
                if L2 > cap2:
                    continue
                for (a0, x1) in la:
                    for (y0, b1) in lb:
                        combos += 1
                        L = (a0 + y0, b1 + x1, L2)
                        if L in found or not inW(L):
                            continue
                        found[L] = (wA[(A2, a0, x1)], wB[(B2, y0, b1)], (kc, vc))
        if log is not None and done % 200 == 0:
            log("C reps %d/%d, combos %d, vectors %d, %.0fs"
                % (done, len(Creps), combos, len(found), time.time() - t0))
    return found, True, {"creps_done": done, "combos": combos}


def affine_relaxed(M2, inW):
    """Union >= max relaxation for affine roots at height 3, restricted to W."""
    out = set()
    for kids in itertools.product(M2, repeat=3):
        for s in range(3):
            L = tuple(max(k[t] for k in kids) if t == s else sum(k[t] for k in kids)
                      for t in range(3))
            if inW(L):
                out.add(L)
    return out


def quad_min(M, best_init=INF):
    """Least (A0+max(B0,C0))(B1+max(A1,C1))(C2+max(A2,B2)) over ordered (A,B,C) in M^3 that is
    below best_init (copied from sticky_pi4.py, where it is tested against brute force)."""
    M = [tuple(v) for v in M]
    if not M:
        return best_init, None
    Ms = sorted(M, key=lambda v: v[2])
    c2min = Ms[0][2]
    best = best_init
    wit = None
    for A in M:
        a0, a1, a2 = A
        for B in M:
            b0, b1, b2 = B
            s0 = a0 + b0
            s1 = a1 + b1
            mab = a2 if a2 > b2 else b2
            base = s0 * s1
            if base * (c2min + mab) >= best:
                continue
            for C in Ms:
                c0, c1, c2 = C
                l2 = c2 + mab
                if base * l2 >= best:
                    break
                l0 = a0 + (b0 if b0 > c0 else c0)
                l1 = b1 + (a1 if a1 > c1 else c1)
                p = l0 * l1 * l2
                if p < best:
                    best = p
                    wit = {"children": [list(A), list(B), list(C)], "L": [l0, l1, l2]}
    return best, wit


# ---------------------------------------------------------------- the job

def run(out_path, tlimit=30000.0):
    t0 = time.time()
    log = lambda s: print(s, flush=True)
    G = group_elements()
    tabs = mask_tables(G)
    rng = random.Random(20261119)
    trees = list(enumerate_height2())
    trees_seen = len(trees)
    vecs2 = set((PC[m0], PC[m1], PC[m2]) for m0, m1, m2, _ in trees)
    allset = set(m0 | (m1 << 9) | (m2 << 18) for m0, m1, m2, _ in trees)
    TA, TB, TC = build_tables(trees)
    del trees
    D = len(allset)
    bugs = []
    for key in rng.sample(sorted(allset), 3000):
        m0, m1, m2 = key & 511, (key >> 9) & 511, key >> 18
        for t in tabs:
            if (t[m0] | (t[m1] << 9) | (t[m2] << 18)) not in allset:
                bugs.append("group image of a height-2 tree is not a tree")
                break
        if bugs:
            break
    del allset
    M2 = minimal3(vecs2)
    log("height 2: %d trees, %d distinct mask triples, %d vectors, %d minimal; tables %d/%d/%d "
        "(%.0fs)" % (trees_seen, D, len(vecs2), len(M2), len(TA), len(TB), len(TC),
                     time.time() - t0))
    if len(vecs2) != 96 or len(M2) != 19:
        bugs.append("height-2 counts differ from a189 (96 vectors, 19 minimal)")
    F3 = game_front3(M2)
    if len(F3) != 112 or min(a * b * c for a, b, c in F3) != 512:
        bugs.append("game front at height 3 differs from sticky-front-v1 (112 vectors, min 512)")
    vmax = w_tables(F3)
    inW, best = make_inW(vmax)
    caps = caps_of(best)
    F3W = [f for f in F3 if inW(f)]
    log("W: caps %s, %d of %d game-front vectors in W (%.0fs)" % (caps, len(F3W), len(F3),
                                                                   time.time() - t0))
    TA = inclusion_minimal(TA)
    TB = inclusion_minimal(TB)
    TC = inclusion_minimal(TC)
    Creps = orbit_reps(TC, tabs)
    log("inclusion-minimal tables %d/%d/%d, C orbit reps %d (%.0fs)"
        % (len(TA), len(TB), len(TC), len(Creps), time.time() - t0))
    left = tlimit - (time.time() - t0)
    found, complete, stats = exact_quadratic(TA, TB, Creps, inW, caps, tlimit=left, log=log)
    QW = minimal3(found.keys())
    AW = affine_relaxed(M2, inW)
    H3 = minimal3(set(QW) | AW)
    H3set = set(H3)
    # self-checks
    for h in H3:
        if not any(leq(f, h) for f in F3):
            bugs.append("H3 vector %s below the game front (impossible)" % (h,))
            break
    for h in (H3 if complete else []):
        for perm in itertools.permutations(range(3)):
            if tuple(h[i] for i in perm) not in H3set:
                bugs.append("H3 not symmetric under slice permutations: %s" % (h,))
                break
        else:
            continue
        break
    if inW((8, 8, 8)) and not any(leq(h, (8, 8, 8)) for h in H3):
        bugs.append("classical (8,8,8) is in W but not dominated by H3")
    if H3 and min(a * b * c for a, b, c in H3) < 512:
        bugs.append("an H3 vector has product < 512, contradicting Proposition 84")
    q4, w4 = quad_min(H3, TARGET)
    lb4 = min(q4, 9 * 512)
    # game-front vectors in W that no real (or affine-relaxed) height-3 vector attains: since every
    # H3 vector dominates a game vector and the game front is an antichain, these are strictly raised
    raised = [list(f) for f in F3W if f not in H3set]
    if bugs:
        verdict = "BUG"
    elif not complete:
        verdict = "INCOMPLETE"
    elif lb4 >= TARGET:
        verdict = "PI4-EXACT"
    else:
        verdict = "PI4-OPEN"
    wit_trees = {}
    for L in QW:
        (ka, va), (kb, vb), (kc, vc) = found[L]
        wit_trees[str(list(L))] = {
            "A": decode(va % CODE), "B": decode(vb % CODE), "C": decode(vc % CODE)}
    out = {
        "job": "sticky-h3-v1",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "height2": {"trees": trees_seen, "distinct_mask_triples": D, "vectors": len(vecs2),
                    "minimal": [list(v) for v in M2]},
        "game_front3": {"size": len(F3), "in_W": [list(f) for f in F3W]},
        "W": {"caps": list(caps), "target": TARGET},
        "tables": {"A": len(TA), "B": len(TB), "C": len(TC), "C_orbit_reps": len(Creps)},
        "exact_quadratic_in_W": [list(v) for v in QW],
        "affine_relaxed_in_W": sorted(list(v) for v in minimal3(AW)) if AW else [],
        "H3": [list(v) for v in H3],
        "game_vectors_raised_by_exact_unions": raised,
        "witness_root_map_height3": [0, 1, 1],
        "witness_note": "height-3 tree = root map g(x) = x^2 = (0,1,1) with child x=0 -> A, "
                        "x=1 -> B, x=2 -> C; each child is (root map, three child maps) of height 2",
        "witness_trees_height3": {k: {"A_root_h0_h1_h2": [list(ALL_MAPS[i]) for i in w["A"]],
                                      "B_root_h0_h1_h2": [list(ALL_MAPS[i]) for i in w["B"]],
                                      "C_root_h0_h1_h2": [list(ALL_MAPS[i]) for i in w["C"]]}
                                  for k, w in wit_trees.items()},
        "height4": {"quad_min_below_4096": q4 if q4 < TARGET else None, "quad_witness": w4,
                    "affine_lower_bound": 9 * 512, "pi4_lower_bound": lb4, "eight_to_4": TARGET},
        "search": dict(stats, complete=complete),
        "bugs": bugs,
        "verdict": verdict,
        "seconds": round(time.time() - t0, 1),
    }
    with open(out_path, "w") as fh:
        json.dump(out, fh, indent=1)
    log("verdict %s, pi4 lower bound %s, H3 size %d" % (verdict, lb4, len(H3)))
    return out


if __name__ == "__main__":
    args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
    run(args.get("--out", "h3.json"), float(args.get("--tlimit", 30000)))
