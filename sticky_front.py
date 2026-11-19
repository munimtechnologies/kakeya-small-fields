# sticky_front.py -- the selection game for sticky Kakeya configurations over F_3
# (pre-registration notes/prereg-sticky-front.md, Lemmas 149-151).
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.
#
# A sticky configuration in F_3^n is a ternary tree of depth n.  The node at a prefix a carries a
# map g_a: F_3 -> F_3 (coordinate j of the base point as a function of d_j, given d_<j = a).  Every
# map of F_3 is either AFFINE with constant slice s (slice s merges all three children, the other
# two slices separate them) or a TRIANGLE (each slice t merges one pair and isolates the third
# child, and t -> isolated child is a bijection).  Lemma 149: |Im Y_t| >= L_t, where
#   leaf: L = (1, 1, 1)
#   affine(s):  L_s = max_x L_s(x),   L_t = sum_x L_t(x)  (t != s)
#   triangle:   L_t = L_t(iso(t)) + max_{x != iso(t)} L_t(x)
# so every sticky Kakeya set K in F_3^n has |K| >= max_t L_t(root) - 1.
# f(h) = min over trees of height h of max_t L_t.  Since triangles everywhere give 2^h, f(h) <= 2^h.
# This module computes the exact Pareto fronts of achievable vectors (pruned at max <= U) and f(h).
# Only stdlib at import time; numpy is used by next_front_np (the job), never by the tests.

import itertools
import json
import sys
import time

LEAF = (1, 1, 1)


def affine(children, s):
    """Parent vector of an affine node whose constant slice is s."""
    p = []
    for t in range(3):
        vals = [c[t] for c in children]
        p.append(max(vals) if t == s else sum(vals))
    return tuple(p)


def triangle(children, iso=(0, 1, 2)):
    """Parent vector of a triangle node; iso[t] = index of the child isolated in slice t."""
    p = []
    for t in range(3):
        i = iso[t]
        others = [children[x][t] for x in range(3) if x != i]
        p.append(children[i][t] + max(others))
    return tuple(p)


def leq(a, b):
    return a[0] <= b[0] and a[1] <= b[1] and a[2] <= b[2]


def pareto_min(vectors):
    """Minimal elements (componentwise order), simple quadratic version."""
    front = []
    for v in sorted(set(vectors)):
        if not any(leq(f, v) for f in front):
            front.append(v)
    return front


def pareto_min_fast(vectors):
    """Same result as pareto_min, using a Fenwick tree of prefix minima over the 2nd coordinate.
    Lexicographic order puts every vector that is <= v (and != v) before v."""
    pts = sorted(set(vectors))
    if not pts:
        return []
    ymax = max(v[1] for v in pts)
    inf = float("inf")
    tree = [inf] * (ymax + 2)
    front = []
    for v in pts:
        i, best = v[1] + 1, inf
        while i > 0:
            if tree[i] < best:
                best = tree[i]
            i -= i & -i
        if best <= v[2]:
            continue
        front.append(v)
        i = v[1] + 1
        while i < len(tree):
            if v[2] < tree[i]:
                tree[i] = v[2]
            i += i & -i
    return front


def next_front_py(front, U=None):
    """Pure-Python step: all children triples from the front, 3 affine ops + triangle.
    Ordered triples with the identity bijection cover every triangle map."""
    out = []
    for c in itertools.product(front, repeat=3):
        for p in (triangle(c), affine(c, 0), affine(c, 1), affine(c, 2)):
            if U is None or max(p) <= U:
                out.append(p)
    return pareto_min_fast(out)


def _harvest(np, p0, p1, p2, U):
    mask = (p0 <= U) & (p1 <= U) & (p2 <= U)
    if not mask.any():
        return []
    base = U + 1
    keys = np.unique((p0[mask] * base + p1[mask]) * base + p2[mask])
    vecs = [(int(k // (base * base)), int((k // base) % base), int(k % base)) for k in keys]
    return pareto_min_fast(vecs)


def _ops_np(np, A, i):
    """Yield (name, p0, p1, p2) arrays over (v, w) in front x front for row0 = A[i]."""
    c0, c1, c2 = A[:, 0], A[:, 1], A[:, 2]
    u0, u1, u2 = (int(x) for x in A[i])
    yield ("triangle",
           u0 + np.maximum(c0[:, None], c0[None, :]),
           c1[:, None] + np.maximum(u1, c1[None, :]),
           c2[None, :] + np.maximum(u2, c2[:, None]))
    cols, us = (c0, c1, c2), (u0, u1, u2)
    mx = [np.maximum(np.maximum(us[t], cols[t][:, None]), cols[t][None, :]) for t in range(3)]
    sm = [us[t] + cols[t][:, None] + cols[t][None, :] for t in range(3)]
    for s in range(3):
        P = [mx[t] if t == s else sm[t] for t in range(3)]
        yield ("affine%d" % s, P[0], P[1], P[2])


def next_front_np(front, U):
    import numpy as np
    A = np.array(front, dtype=np.int64)
    acc = []
    for i in range(len(front)):
        for _name, p0, p1, p2 in _ops_np(np, A, i):
            acc.extend(_harvest(np, p0, p1, p2, U))
        if len(acc) > 200000:
            acc = pareto_min_fast(acc)
    return pareto_min_fast(acc)


def derive_np(target, front):
    """Find one (op, (u, v, w)) with children in front producing exactly target."""
    import numpy as np
    A = np.array(front, dtype=np.int64)
    for i in range(len(front)):
        for name, p0, p1, p2 in _ops_np(np, A, i):
            hit = np.argwhere((p0 == target[0]) & (p1 == target[1]) & (p2 == target[2]))
            if len(hit):
                j, k = (int(x) for x in hit[0])
                return name, (tuple(front[i]), tuple(front[j]), tuple(front[k]))
    return None


def summary(front, h):
    f = min(max(v) for v in front)
    mm = min(min(v) + max(v) for v in front)
    prod = min(v[0] * v[1] * v[2] for v in front)
    pair = min(min(v[0] * v[1], v[0] * v[2], v[1] * v[2]) for v in front)
    return {
        "h": h, "front_size": len(front), "f": f, "two_pow_h": 2 ** h, "f_equals_2h": f == 2 ** h,
        "argmin_f": sorted(v for v in front if max(v) == f)[:12],
        "min_minplusmax": mm, "M_holds": mm >= 2 ** (h + 1),
        "min_product_pruned": prod, "P_holds_pruned": prod >= 8 ** h,
        "lemma150_pair_ok": pair >= 3 ** h,
        "entropy_ok": all(4 ** h * v[0] * v[1] * v[2] >= 27 ** h for v in front),
    }


def run(hmax, fcap, tlimit, out_path):
    U = 2 ** hmax
    t0 = time.time()
    fronts = [[LEAF]]
    # self-check: numpy step equals the pure-Python step on the first fronts
    for h in range(3):
        a = next_front_np(fronts[-1], U)
        b = next_front_py(fronts[-1], U)
        if a != b:
            raise SystemExit("SELF-CHECK FAILED at h=%d: numpy and python fronts differ" % (h + 1))
        fronts.append(a)
    report = {"U": U, "hmax": hmax, "fcap": fcap, "selfcheck": "ok", "heights": [], "stop": "done",
              "witnesses": {}}
    for h, fr in enumerate(fronts[1:], start=1):
        report["heights"].append(summary(fr, h))
    h = len(fronts) - 1
    while h < hmax:
        if len(fronts[-1]) > fcap:
            report["stop"] = "front size %d > fcap at h=%d" % (len(fronts[-1]), h)
            break
        if time.time() - t0 > tlimit:
            report["stop"] = "time limit before h=%d" % (h + 1)
            break
        ts = time.time()
        nf = next_front_np(fronts[-1], U)
        fronts.append(nf)
        h += 1
        s = summary(nf, h)
        s["seconds"] = round(time.time() - ts, 1)
        report["heights"].append(s)
        if not s["f_equals_2h"]:
            tgt = s["argmin_f"][0]
            report["witnesses"][str(h)] = {"vector": tgt, "derivation": derive_np(tgt, fronts[h - 1])}
        with open(out_path, "w") as fh:
            json.dump(report, fh, indent=1)
        print(json.dumps(s), flush=True)
    report["fronts_small"] = {str(k): fronts[k] for k in range(len(fronts)) if len(fronts[k]) <= 400}
    report["seconds_total"] = round(time.time() - t0, 1)
    with open(out_path, "w") as fh:
        json.dump(report, fh, indent=1)
    return report


if __name__ == "__main__":
    args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
    run(int(args.get("--hmax", 9)), int(args.get("--fcap", 2000)),
        float(args.get("--tlimit", 12600)), args.get("--out", "sticky_front.json"))
