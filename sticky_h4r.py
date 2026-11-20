# sticky_h4r.py -- exact unions at height 3, union >= max relaxation at heights 4 and 5:
# a proved lower bound for pi_5 (and, time permitting, pi_6).
# Notes a188-a194; pre-registration notes/prereg-sticky-h4r.md.
#
# Setting (a188).  A full sticky tree of height k over F_3 is a sticky map P: F_3^k -> F_3^k; its
# slices are S_t = {P(d) + t d}, t = 0, 1, 2, and pi_k is the least |S_0||S_1||S_2|.  Question S7
# (is the sticky Kakeya growth base over F_3 below 2?) holds iff pi_k < 8^k for some k
# (Theorem 78 / Corollary 78.1).  Proved so far: pi_1 = 8, pi_2 = 64, pi_3 = 512 (a189),
# pi_4 = 4096 (a194, Proposition 88, from sticky-h3-v1).  The pure max-relaxation ("game") of a190
# allows 27,000 < 32,768 at height 5, so it cannot decide pi_5.
#
# This module keeps height 3 EXACT on the whole range (sticky_h3.py restricted it to the down-set W
# that matters for height 4) and relaxes only above it:
#   E3 = coordinatewise-minimal (exact quadratic height-3 vectors  u  affine-relaxed ones),
#   F4 = game front one level up from E3, F5 = one more level (optional).
# Every real height-k vector dominates an element of the front at height k, the node bound is
# monotone, so
#   pi_5 >= min( least quadratic-root product over F4,  9 * pi_4 = 36,864 )   (Lemma 162)
# and similarly pi_6 >= min( least quadratic-root product over F5, 9 * (bound for pi_5) ).
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only; needs sticky_h3.py (same directory).

import itertools
import json
import sys
import time

import sticky_h3 as h3

INF = h3.INF
PC = h3.PC
T4 = 8 ** 4            # 4096
T5 = 8 ** 5            # 32768
T6 = 8 ** 6            # 262144
H3_IN_W = [(4, 12, 12), (12, 4, 12), (12, 12, 4)]    # sticky-h3-v1 (a194)


# ---------------------------------------------------------------- fronts

def front_from_best2(best2):
    """best2: dict (v0, v1) -> least v2 seen.  Returns the sorted list of coordinatewise-minimal
    vectors (v0, v1, v2) among all vectors recorded (a vector with the same (v0, v1) and larger v2
    is dominated by the recorded one, so best2 loses nothing)."""
    if not best2:
        return []
    top = max(max(i for i, _ in best2), max(j for _, j in best2))
    # P[i][j] = least v2 over recorded (u0, u1) with u0 <= i and u1 <= j
    P = [[INF] * (top + 1) for _ in range(top + 1)]
    for i in range(top + 1):
        Pi = P[i]
        Pm = P[i - 1] if i > 0 else None
        for j in range(top + 1):
            x = best2.get((i, j), INF)
            if Pm is not None and Pm[j] < x:
                x = Pm[j]
            if j > 0 and Pi[j - 1] < x:
                x = Pi[j - 1]
            Pi[j] = x
    out = []
    for (i, j), v in best2.items():
        below = INF
        if i > 0 and P[i - 1][j] < below:
            below = P[i - 1][j]
        if j > 0 and P[i][j - 1] < below:
            below = P[i][j - 1]
        if v < below:
            out.append((i, j, v))
    out.sort()
    return out


def next_front(F, witness=None):
    """Front one level up: coordinatewise-minimal node vectors over ordered child triples from F and
    all 27 root maps, in closed form.  A quadratic root gives triangle(A, B, C) =
    (A0 + max(B0, C0), B1 + max(A1, C1), C2 + max(A2, B2)) after relabelling the children (the
    isolated child of slice t is a bijection of t, Lemma 162); an affine root puts all three
    children in one plane in exactly one slice s (union >= max there) and in three different planes
    in the other two (sums).  If witness is a dict, witness[(v0, v1)] records (kind, A, B, C) for
    the best v2 found."""
    F = sorted(set(tuple(v) for v in F))
    best2 = {}
    get = best2.get
    rec = witness is not None
    for A in F:
        a0, a1, a2 = A
        for B in F:
            b0, b1, b2 = B
            m2 = a2 if a2 > b2 else b2
            mx0 = a0 if a0 > b0 else b0
            mx1 = a1 if a1 > b1 else b1
            s0 = a0 + b0
            s1 = a1 + b1
            s2 = a2 + b2
            for C in F:
                c0, c1, c2 = C
                # quadratic root
                k = (a0 + (b0 if b0 > c0 else c0), b1 + (a1 if a1 > c1 else c1))
                v = c2 + m2
                if v < get(k, INF):
                    best2[k] = v
                    if rec:
                        witness[k] = ("quadratic", A, B, C)
                # affine root, one plane in slice 0
                v = s2 + c2
                k = (mx0 if mx0 > c0 else c0, s1 + c1)
                if v < get(k, INF):
                    best2[k] = v
                    if rec:
                        witness[k] = ("affine-slice-0", A, B, C)
                # affine root, one plane in slice 1
                k = (s0 + c0, mx1 if mx1 > c1 else c1)
                if v < get(k, INF):
                    best2[k] = v
                    if rec:
                        witness[k] = ("affine-slice-1", A, B, C)
                # affine root, one plane in slice 2
                k = (s0 + c0, s1 + c1)
                v = m2 if m2 > c2 else c2
                if v < get(k, INF):
                    best2[k] = v
                    if rec:
                        witness[k] = ("affine-slice-2", A, B, C)
    return front_from_best2(best2)


def prod(v):
    return v[0] * v[1] * v[2]


def dominates_some(v, F):
    return any(h3.leq(f, v) for f in F)


def tree_of(found, L):
    """Height-3 witness tree for an exact quadratic vector L (root map x^2 = (0,1,1))."""
    (ka, va), (kb, vb), (kc, vc) = found[L]
    out = {}
    for name, val in (("A", va), ("B", vb), ("C", vc)):
        r, a, b, c = h3.decode(val % h3.CODE)
        out[name + "_root_h0_h1_h2"] = [list(h3.ALL_MAPS[i]) for i in (r, a, b, c)]
    return out


# ---------------------------------------------------------------- the job

def run(out_path, tlimit=9000.0, h6=True, h6_max_front=900):
    t0 = time.time()
    log = lambda s: print(s, flush=True)
    bugs = []
    out = {"job": "sticky-h4r-v1",
           "made_with": "AI agents working in MV2's name; no human has checked this"}

    def save():
        out["bugs"] = bugs
        out["seconds"] = round(time.time() - t0, 1)
        with open(out_path, "w") as fh:
            json.dump(out, fh, indent=1)

    # ---- height 2, exhaustively (as in sticky_h3.py)
    G = h3.group_elements()
    tabs = h3.mask_tables(G)
    trees = list(h3.enumerate_height2())
    n_trees = len(trees)
    vecs2 = set((PC[m0], PC[m1], PC[m2]) for m0, m1, m2, _ in trees)
    TA, TB, TC = h3.build_tables(trees)
    del trees
    M2 = h3.minimal3(vecs2)
    if n_trees != 27 ** 4 or len(vecs2) != 96 or len(M2) != 19:
        bugs.append("height-2 counts differ from a189 (531441 trees, 96 vectors, 19 minimal)")
    log("height 2: %d trees, %d vectors, %d minimal (%.0fs)"
        % (n_trees, len(vecs2), len(M2), time.time() - t0))

    # ---- the pure game (a190), as a check of next_front
    F3 = h3.game_front3(M2)
    F3b = next_front(M2)
    if sorted(F3) != F3b:
        bugs.append("next_front(M2) differs from the node-by-node game front at height 3")
    if len(F3) != 112 or min(prod(f) for f in F3) != 512:
        bugs.append("game front at height 3 differs from sticky-front-v1 (112 vectors, min 512)")
    G4 = next_front(F3)
    g4min = min(prod(v) for v in G4)
    if len(G4) != 649 or g4min != 3971:
        bugs.append("game front at height 4 differs from sticky-front-v1 (649 vectors, min 3971)")
    g5, g5w = h3.quad_min(G4, T5)
    if g5 != 27000:
        bugs.append("game height-5 quadratic minimum %s differs from sticky-front-v1 (27000)" % g5)
    out["game"] = {"front3": len(F3), "front4": len(G4), "front4_min_product": g4min,
                   "height5_quadratic_min": g5, "height5_witness": g5w}
    log("game: fronts 112 -> %d (min %d), height-5 quadratic min %s (%.0fs)"
        % (len(G4), g4min, g5, time.time() - t0))

    # ---- exact height 3, whole range
    TA = h3.inclusion_minimal(TA)
    TB = h3.inclusion_minimal(TB)
    TC = h3.inclusion_minimal(TC)
    Creps = h3.orbit_reps(TC, tabs)
    everything = lambda L: True
    left = tlimit - (time.time() - t0)
    found, complete, stats = h3.exact_quadratic(TA, TB, Creps, everything, (27, 27, 27),
                                                tlimit=left, log=log)
    QF = h3.minimal3(found.keys())
    AF = h3.affine_relaxed(M2, everything)
    AFmin = h3.minimal3(AF)
    E3 = h3.minimal3(set(QF) | AF)
    E3set = set(E3)
    QFset = set(QF)
    log("exact height 3: %d quadratic vectors (%d minimal), %d affine-relaxed minimal, "
        "front E3 %d, complete %s (%.0fs)"
        % (len(found), len(QF), len(AFmin), len(E3), complete, time.time() - t0))
    if E3 and min(prod(e) for e in E3) != 512:
        bugs.append("least product on E3 is not 512 (Proposition 84)")
    for e in E3:
        if not dominates_some(e, F3):
            bugs.append("E3 vector %s lies below the game front (impossible)" % (e,))
            break
    if complete:
        for e in E3:
            if any(tuple(e[i] for i in p) not in E3set for p in itertools.permutations(range(3))):
                bugs.append("E3 not symmetric under slice permutations: %s" % (e,))
                break
    if not dominates_some((8, 8, 8), E3):
        bugs.append("classical (8,8,8) not dominated by E3")
    vmax = h3.w_tables(F3)
    inW, _best = h3.make_inW(vmax)
    E3W = sorted(e for e in E3 if inW(e))
    if complete and E3W != sorted(H3_IN_W):
        bugs.append("E3 restricted to W is %s, not sticky-h3-v1's H3" % (E3W,))
    raised3 = [list(f) for f in F3 if f not in E3set]
    out["height3"] = {"exact_quadratic_vectors": len(found), "exact_quadratic_minimal": len(QF),
                      "affine_relaxed_minimal": len(AFmin), "E3_size": len(E3),
                      "E3": [list(e) for e in E3],
                      "E3_kind": {str(list(e)): ("exact-quadratic" if e in QFset else
                                                 "affine-relaxed") for e in E3},
                      "E3_in_W": [list(e) for e in E3W],
                      "game_front3_vectors_raised": len(raised3),
                      "game_front3_vectors_kept": len(F3) - len(raised3),
                      "search": dict(stats, complete=complete)}
    if not complete:
        out["verdict"] = "INCOMPLETE"
        save()
        log("verdict INCOMPLETE")
        return out

    # ---- height 4 and the bound for pi_5
    t4 = time.time()
    wit4 = {}
    F4 = next_front(E3, wit4)
    sec4 = time.time() - t4
    f4min = min(prod(v) for v in F4)
    if f4min != T4:
        bugs.append("least product on F4 is %d, not 4096 (Proposition 88)" % f4min)
    f4maxmin = min(max(v) for v in F4)
    g4set = set(G4)
    q5, w5 = h3.quad_min(F4, T5)
    lb5 = min(q5, 9 * T4)
    smallest4 = sorted(F4, key=lambda v: (prod(v), v))[:30]
    out["height4"] = {"F4_size": len(F4), "F4_min_product": f4min,
                      "F4_min_max_coordinate": f4maxmin,
                      "F4_vectors_also_in_game_front4": sum(1 for v in F4 if v in g4set),
                      "smallest_products": [[list(v), prod(v)] for v in smallest4],
                      "seconds": round(sec4, 1)}
    deriv = {}
    if w5 is not None:
        for v in w5["children"]:
            v = tuple(v)
            kind, A, B, C = wit4[(v[0], v[1])]
            kids = {}
            for name, e in (("A", A), ("B", B), ("C", C)):
                kids[name] = {"vector": list(e),
                              "kind": "exact-quadratic" if e in QFset else "affine-relaxed"}
                if e in QFset:
                    kids[name]["tree"] = tree_of(found, e)
            deriv[str(list(v))] = {"root": kind, "children": kids}
    out["height5"] = {"quadratic_min_below_32768": q5 if q5 < T5 else None,
                      "quadratic_witness": w5, "witness_derivations": deriv,
                      "affine_lower_bound": 9 * T4, "pi5_lower_bound": lb5,
                      "eight_to_5": T5, "game_value": 27000}
    if bugs:
        verdict = "BUG"
    elif lb5 >= T5:
        verdict = "PI5-EXACT"
    else:
        verdict = "PI5-OPEN"
    out["verdict"] = verdict
    save()
    log("F4 %d vectors (min product %d, %.0fs); pi5 lower bound %d; verdict %s"
        % (len(F4), f4min, sec4, lb5, verdict))

    # ---- optional: height 5 front and a bound for pi_6
    if h6 and not bugs:
        per = sec4 / max(1, len(E3)) ** 3
        predicted = per * len(F4) ** 3
        remaining = tlimit - (time.time() - t0)
        out["height6_plan"] = {"predicted_seconds": round(predicted), "remaining": round(remaining)}
        if len(F4) <= h6_max_front and predicted < 0.6 * remaining:
            t5 = time.time()
            F5 = next_front(F4)
            q6, w6 = h3.quad_min(F5, T6)
            lb6 = min(q6, 9 * min(lb5, T5))
            out["height6"] = {"F5_size": len(F5), "F5_min_product": min(prod(v) for v in F5),
                              "F5_min_max_coordinate": min(max(v) for v in F5),
                              "quadratic_min_below_262144": q6 if q6 < T6 else None,
                              "quadratic_witness": w6, "affine_lower_bound": 9 * min(lb5, T5),
                              "pi6_lower_bound": lb6, "eight_to_6": T6,
                              "seconds": round(time.time() - t5, 1)}
            log("F5 %d vectors; pi6 lower bound %d (%.0fs)" % (len(F5), lb6, time.time() - t5))
        else:
            out["height6"] = None
            log("height 6 skipped (front %d, predicted %.0fs)" % (len(F4), predicted))
        save()
    return out


if __name__ == "__main__":
    args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
    run(args.get("--out", "h4r.json"), float(args.get("--tlimit", 9000)),
        args.get("--h6", "1") == "1")
