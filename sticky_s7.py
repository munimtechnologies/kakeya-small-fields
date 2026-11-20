# sticky_s7.py -- an explicit sticky tree over F_3 with slice product below 8^k (note a196).
#
# Setting (a188).  A full sticky tree of height k over F_3 is a map P: F_3^k -> F_3^k whose
# coordinate j depends only on d_1, ..., d_j.  Its slices are S_t = {P(d) + t d}, t = 0, 1, 2.
# Corollary 78.1: sticky Kakeya sets over F_3 grow with base below 2 (question S7) iff some tree
# has |S_0| |S_1| |S_2| < 8^k.
#
# This module builds, by brute force and with no search, the trees of note a196:
#   A (height 3)  P(d) = (d1^2, -d1 d2, 0)                       slices (4, 12, 12), A_1 = A_2
#   B (height 3)  the (7, 7, 13) tree of note a187                B_2 contains A_1 u A_2
#   C (height 3)  C(e) = B(-e)                                    slices (B_0, B_2, B_1)
#   H (height 4)  root x^2 over children (A, B, C)                slices (11, 20, 20), H_1 = H_2
#   G (height 5)  cyclic triangle of H (Prop 89): root x^2 over (H, H + 2d, H + d)
#                                                                 slices (31, 31, 31)
# 31^3 = 29,791 < 8^5 = 32,768, so S7 holds and the sticky base is at most 31^(1/5) < 1.98735.
# It also builds the Kakeya set {(t, G(d) + t d)} u {0} x K_5 in F_3^6 and checks that it
# contains a line in every direction.
#
# MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name.
# Licence: Apache-2.0.  Stdlib only, self-contained.

import itertools
import json
import sys


def domain(k):
    return list(itertools.product(range(3), repeat=k))


# ---------------------------------------------------------------- the trees

def tree_A(d):
    """Height 3: P(d1, d2, d3) = (d1^2, -d1 d2, 0)."""
    d1, d2, d3 = d
    return (d1 * d1 % 3, (-d1 * d2) % 3, 0)


def _Y(f):
    return ((-f[0]) % 3, 0)


def _X(f):
    return (1, (-f[1]) % 3)


def _Z(f):
    return (f[0] * f[0] % 3, (-f[0] * f[1]) % 3)


def tree_B(e):
    """Height 3, note a187: root e1 -> e1^2 with height-2 children Y, X, Z under e1 = 0, 1, 2."""
    return (e[0] * e[0] % 3,) + (_Y, _X, _Z)[e[0]](e[1:])


def tree_C(e):
    """C(e) = B(-e); its slices are (B_0, B_2, B_1) as sets."""
    return tree_B(tuple((-x) % 3 for x in e))


def tree_H(d):
    """Height 4: root d1 -> d1^2 with children A, B, C under d1 = 0, 1, 2."""
    return (d[0] * d[0] % 3,) + (tree_A, tree_B, tree_C)[d[0]](d[1:])


def rho(P, c):
    """rho_c(P)(d) = P(d) + c d (a188, Lemma 161): S_t(rho_c P) = S_{t+c}(P)."""
    def Q(d):
        return tuple((p + c * x) % 3 for p, x in zip(P(d), d))
    return Q


_H_PLUS_2D = rho(tree_H, 2)
_H_PLUS_D = rho(tree_H, 1)


def tree_G(d):
    """Height 5: the cyclic triangle of H with i = 0, w = 0 (note a195, Proposition 89)."""
    return (d[0] * d[0] % 3,) + (tree_H, _H_PLUS_2D, _H_PLUS_D)[d[0]](d[1:])


def classical(d):
    """The classical tree P(d) = (d_j^2)_j, any height."""
    return tuple(x * x % 3 for x in d)


# ---------------------------------------------------------------- checks

def slices(P, k):
    out = []
    for t in range(3):
        out.append(frozenset(tuple((p + t * x) % 3 for p, x in zip(P(d), d))
                             for d in domain(k)))
    return out


def is_sticky(P, k):
    """Coordinate j of P(d) depends only on d_1, ..., d_j (and P maps into F_3^k)."""
    dom = domain(k)
    vals = {d: P(d) for d in dom}
    for d, v in vals.items():
        if len(v) != k or any(x not in (0, 1, 2) for x in v):
            return False
    for j in range(k):
        seen = {}
        for d in dom:
            key = d[:j + 1]
            if seen.setdefault(key, vals[d][j]) != vals[d][j]:
                return False
    return True


def translate(S, w):
    return frozenset(tuple((a + b) % 3 for a, b in zip(p, w)) for p in S)


def kappa(P, k):
    """kappa(P) = min over i, w of |S_i| + |S_{i+1} u (S_{i+2} + w)| (note a195)."""
    S = slices(P, k)
    best = None
    arg = None
    for i in range(3):
        for w in domain(k):
            v = len(S[i]) + len(S[(i + 1) % 3] | translate(S[(i + 2) % 3], w))
            if best is None or v < best:
                best, arg = v, (i, list(w))
    return best, arg


def kakeya_from(P, k, lower):
    """{(t, P(d) + t d)} u {0} x lower: lines in all directions (1, d) and, if lower is a Kakeya
    set in F_3^k, in all directions (0, v)."""
    K = set((0,) + tuple(y) for y in lower)
    for d in domain(k):
        p = P(d)
        for t in range(3):
            K.add((t,) + tuple((a + t * b) % 3 for a, b in zip(p, d)))
    return K


def is_kakeya(K, n):
    """Every direction v != 0 (first non-zero coordinate 1) has a line x + F_3 v inside K."""
    for v in domain(n):
        nz = [x for x in v if x]
        if not nz or nz[0] != 1:
            continue
        found = False
        for x in K:
            y = tuple((a + b) % 3 for a, b in zip(x, v))
            if y in K and tuple((a + 2 * b) % 3 for a, b in zip(x, v)) in K:
                found = True
                break
        if not found:
            return False
    return True


def classical_kakeya(n):
    """K_1 = F_3 and K_{m+1} = {(t, classical(d) + t d)} u {0} x K_m."""
    K = set((t,) for t in range(3))
    for m in range(1, n):
        K = kakeya_from(classical, m, K)
    return K


def sorted_lists(S):
    return [list(p) for p in sorted(S)]


def run(out_path=None):
    res = {"job": "sticky-s7", "note": "a196",
           "made_with": "AI agents working in MV2's name; no human has checked this"}
    trees = {"A": (tree_A, 3), "B": (tree_B, 3), "C": (tree_C, 3), "H": (tree_H, 4),
             "G": (tree_G, 5)}
    S = {}
    for name, (P, k) in trees.items():
        S[name] = slices(P, k)
        res[name] = {"height": k, "sticky": is_sticky(P, k),
                     "slice_sizes": [len(s) for s in S[name]],
                     "S1_equals_S2": S[name][1] == S[name][2]}
    for name in ("A", "B"):
        res[name]["slices"] = [sorted_lists(s) for s in S[name]]
    res["C"]["slices_are_B_0_B_2_B_1"] = (S["C"][0] == S["B"][0] and S["C"][1] == S["B"][2]
                                         and S["C"][2] == S["B"][1])
    res["A1_union_A2_subset_B2"] = (S["A"][1] | S["A"][2]) <= S["B"][2]
    kH, argH = kappa(tree_H, 4)
    res["H"]["kappa"] = kH
    res["H"]["kappa_argmin_i_w"] = argH
    gs = [len(s) for s in S["G"]]
    res["G"]["product"] = gs[0] * gs[1] * gs[2]
    res["eight_to_5"] = 8 ** 5
    cs = [len(s) for s in slices(classical, 5)]
    res["classical_height5_product"] = cs[0] * cs[1] * cs[2]
    res["base_upper_bound"] = round(31 ** 0.2, 5)
    K5 = classical_kakeya(5)
    K6 = kakeya_from(tree_G, 5, K5)
    res["kakeya_F3_5_classical"] = {"size": len(K5), "is_kakeya": is_kakeya(K5, 5)}
    res["kakeya_F3_6_from_G"] = {"size": len(K6), "is_kakeya": is_kakeya(K6, 6)}
    ok = (all(res[n]["sticky"] for n in trees) and res["G"]["slice_sizes"] == [31, 31, 31]
          and res["G"]["product"] < 8 ** 5 and res["A1_union_A2_subset_B2"]
          and res["kakeya_F3_6_from_G"]["is_kakeya"])
    res["verdict"] = "S7-TRUE" if ok else "CHECK-FAILED"
    if out_path:
        with open(out_path, "w") as fh:
            json.dump(res, fh, indent=1)
    return res


if __name__ == "__main__":
    args = dict(zip(sys.argv[1::2], sys.argv[2::2]))
    r = run(args.get("--out", "s7.json"))
    print("verdict", r["verdict"], "H", r["H"]["slice_sizes"], "kappa(H)", r["H"]["kappa"],
          "G", r["G"]["slice_sizes"], "product", r["G"]["product"])
