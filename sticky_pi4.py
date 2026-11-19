# sticky_pi4.py -- a proved lower bound for pi_4 (notes a188, a189): the least slice product
# |S_0||S_1||S_2| of a full sticky tree of height 4 over F_3.
#
# Method (a "hybrid relaxation"): every real slice-size vector of height 2 is known exhaustively
# (sticky_pi3.height2_vectors).  Above height 2 each union of children's slices that share a plane
# is replaced by the MAX of their sizes.  Union >= max, and max and sum are monotone, so:
#   * every real height-3 vector dominates (coordinatewise) a vector of M3, the minimal elements
#     of R3 = { node_lower(root, kids) : kids in M2^3, root any of the 27 maps };
#   * every real height-4 vector dominates node_lower(root, kids) for some kids in M3^3.
# Quadratic roots: in slice t one child iso(t) is alone in its plane and the other two share one,
# with iso a bijection (a188, Lemma 162); after relabelling the children iso = identity, so
#   L = (A0 + max(B0, C0), B1 + max(A1, C1), C2 + max(A2, B2))  over ordered (A, B, C) in M3^3.
# Affine roots: L_s = max, L_t = sum, so L0 L1 L2 >= 9 (G_A G_B G_C)^(1/3) >= 9 min_M3 G (AM-GM,
# a188 Lemma 162); this is checked against the computed numbers, not assumed.
# If the bound is 4096 = 8^4, then pi_4 = 4096 and no certificate for question S7 has height <= 4.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained (needs sticky_pi3.py).

import itertools
import json
import sys
import time

from sticky_pi3 import ALL_MAPS, height2_vectors, minimal, node_lower

INF = 10 ** 9


def is_affine(root):
    """g is affine iff g(x) + s x is constant for some s in F_3."""
    return any(len({(root[x] + s * x) % 3 for x in range(3)}) == 1 for s in range(3))


def minimal_fast(vecs):
    """Coordinatewise-minimal elements of a set of positive integer 3-vectors (exact)."""
    vecs = set(tuple(v) for v in vecs)
    D = max(max(v) for v in vecs) + 2
    cmin = [[INF] * D for _ in range(D)]
    for a, b, c in vecs:
        if c < cmin[a][b]:
            cmin[a][b] = c
    pm = [[INF] * D for _ in range(D)]
    for a in range(D):
        for b in range(D):
            m = cmin[a][b]
            if a and pm[a - 1][b] < m:
                m = pm[a - 1][b]
            if b and pm[a][b - 1] < m:
                m = pm[a][b - 1]
            pm[a][b] = m
    out = []
    for a, b, c in vecs:
        if c != cmin[a][b]:
            continue
        other = INF
        if a:
            other = min(other, pm[a - 1][b])
        if b:
            other = min(other, pm[a][b - 1])
        if other <= c:
            continue
        out.append((a, b, c))
    return sorted(out)


def relaxed_level(mins):
    """R = { node_lower(root, kids) : kids in mins^3, root in ALL_MAPS }."""
    out = set()
    for kids in itertools.product(mins, repeat=3):
        for root in ALL_MAPS:
            out.add(tuple(node_lower(root, kids)))
    return out


def quad_min(M, best_init=INF):
    """Least (A0+max(B0,C0))(B1+max(A1,C1))(C2+max(A2,B2)) over ordered (A,B,C) in M^3 that is
    below best_init.  Returns (best, witness or None, pairs_examined)."""
    M = [tuple(v) for v in M]
    Ms = sorted(M, key=lambda v: v[2])
    c2min = Ms[0][2]
    best = best_init
    wit = None
    pairs = 0
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
            pairs += 1
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
    return best, wit, pairs


def run(out_path):
    t0 = time.time()
    v2 = height2_vectors()
    M2 = minimal_fast(v2)
    assert M2 == minimal(v2), "minimal_fast disagrees with minimal at height 2"
    # Height 3 (reproduces sticky-beam-v1's pi3 = 512 through the quadratic formula).
    q3, w3, _ = quad_min(M2)
    G2min = min(a * b * c for a, b, c in M2)
    R3 = relaxed_level(M2)
    M3 = minimal_fast(R3)
    G3min = min(a * b * c for a, b, c in M3)
    t1 = time.time()
    print("height 2: %d vectors, %d minimal; height 3: quad min %d, %d relaxed, %d minimal, "
          "least product %d (%.1fs)" % (len(v2), len(M2), q3, len(R3), len(M3), G3min, t1 - t0),
          flush=True)
    # Height 4.
    q4, w4, pairs = quad_min(M3, 4097)
    affine4 = 9 * G3min            # lower bound for every affine root (Lemma 162, AM-GM)
    lb4 = min(q4, affine4)
    t2 = time.time()
    print("height 4: quad min %s, affine bound %d, lower bound %d, pairs %d (%.1fs)"
          % (q4 if q4 < 4097 else ">4096", affine4, lb4, pairs, t2 - t1), flush=True)
    bug = []
    if q3 != 512:
        bug.append("height-3 quadratic minimum %d != 512 (sticky-beam-v1 found 512)" % q3)
    if G2min != 64:
        bug.append("least height-2 product %d != 64 (Proposition 83)" % G2min)
    if G3min < 512:
        bug.append("a relaxed height-3 vector has product %d < 512" % G3min)
    if q4 > 4096:
        bug.append("relaxation exceeds the classical 4096: impossible")
    if lb4 < 3456:
        bug.append("bound %d below (27/4)*512 = 3456 contradicts Lemma 162" % lb4)
    if bug:
        verdict = "BUG"
    elif lb4 >= 4096:
        verdict = "PI4-EXACT"
    else:
        verdict = "PI4-OPEN"
    out = {
        "job": "sticky-pi4-v1",
        "made_with": "AI agents working in MV2's name; no human has checked this",
        "height2": {"vectors": len(v2), "minimal": [list(v) for v in M2], "least_product": G2min},
        "height3": {"quad_min": q3, "quad_witness": w3, "relaxed_vectors": len(R3),
                    "minimal_count": len(M3), "least_product": G3min,
                    "minimal": [list(v) for v in M3]},
        "height4": {"quad_min": q4 if q4 < 4097 else None, "quad_witness": w4,
                    "affine_lower_bound": affine4, "pi4_lower_bound": lb4,
                    "pairs_examined": pairs, "eight_to_4": 4096},
        "bugs": bug,
        "verdict": verdict,
        "seconds": round(time.time() - t0, 1),
    }
    with open(out_path, "w") as fh:
        json.dump(out, fh, indent=1)
    print("verdict", verdict, flush=True)
    return out


if __name__ == "__main__":
    run(sys.argv[1] if len(sys.argv) > 1 else "pi4.json")
