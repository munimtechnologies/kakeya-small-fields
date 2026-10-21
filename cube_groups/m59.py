# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m59: the next passes over (B6) and (B5) at t = 7 and dim V = 9, under rules that jobs m57
and m58 wrote down before they ran (cube_groups/m57-predictions.md, m58-predictions.md;
notes/a48.md).

Group a (job m59a), (B6):
  (1) r3g_t7_B6_o002_a117 and a153, the two instances of the kind-graph class (pair orbit 2) that
      m58a left UNKNOWN at 95 s (both rank 0 on X_1): CaDiCaL for 15 minutes, then, if still open,
      CryptoMiniSat with native XOR for 15 minutes (m58's rule for 1 to 10 open). The other 176 of
      the 178 instances are UNSAT (m54a, m58a), so if both close, the class is empty.
  (2) the kind-L class (pair orbit 0, x0 in Im A_u), split by the second matrix A_(h_1) as
      Proposition 30 splits it: m52 counted 308 classes (51 / 174 / 83 by rank on X_1) in its own
      frame. Here they are counted again, directly in m42's coordinates (x0 = e_0,
      P = span(e_1, ..., e_6), A_u = e_4 -> e_2, e_5 -> e_1, e_6 -> e_0, the representative of
      r3b_t7_B6_o000_c000), and the run goes ahead only if the count gives m52's |G| = 12288,
      |Adm| = 344 * 512 - 2 = 176126, 308 classes and 51 / 174 / 83. CaDiCaL, at most 25 s each.
      If all 308 are UNSAT, the kind-L class is empty.

Group b (job m59b), (B5):
  (1) r3b_t7_B5_o009_c009 and o016_c024 (d = 1), the two classes of batch c with d <= 2 that m57a's
      CaDiCaL left open at 15 minutes: CryptoMiniSat with native XOR, at most 5 minutes each (m57's
      rule: the XOR arm is the second pass for open classes with d <= 2).
  (2) the classes r3b_t7_B5_o002_c000 and o001_c000 (d = 3), split by the second matrix as
      Proposition 32 splits them: the 421 and 445 representatives of job m55, recomputed here by
      m55.py (imported unchanged; its orbit roots are the smallest index in each orbit, so they do
      not depend on the generators drawn) and gated on m55's counts. CaDiCaL, at most 20 s each.
      If every instance of a class is UNSAT, the class is empty.

Instances are m57.py's (m42.py's encoding and hints, m53.py's unit clauses for A_(v_1), m50.py's
XOR encoding), unchanged; m57.py and m55.py are imported, not copied.

Parts:
    check   graded: m57.py's own check; a117 and a153 are admissible with rank 0 on X_1; the two
            (B5) classes have d = 1; kind L: A_u has kernel X_1 and image R with x0 in R, the
            group, |Adm|, the 308 classes and their ranks as m52, the representatives admissible
            and distinct with their sums with A_u; the two (B5) splits as m55 (orders, |Adm|,
            classes and ranks), representatives admissible (Proposition 32 (a), including
            rank(A + A_u) <= 3) and distinct; hint and unit counts of one instance of each kind.
            Writes m59_reps.json, which solve and grade read.
    solve   the group's plan in order.
    grade   graded checks and every SAT verified; statuses by rank on X_1 or by class.

Usage: python m59.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import argparse
import json
import os
import random
import time
from array import array

import m55
import m57 as m
import sat_aniso as sa

T, D = 7, 9
MIN_BUDGET = 10.0
X1 = (8, 4, 2, 1)

# The kind-graph class (pair orbit 2), as m58.py: A_u = e_4 -> e_3, e_5 -> e_2, e_6 -> e_0 + e_1,
# and the two instances m58a left open: (m54 order k, m52 index, rank on X_1, A_(h_1)), copied from
# m58.py's GRAPH_B (entries 28 and 64, that is a117 and a153).
GRAPH_AU = 34086976
GRAPH_R = (8, 4, 3)
GRAPH_OPEN = ((117, 2560, 0, 33556496), (153, 8704, 0, 34078720))
GRAPH_UNSAT_BEFORE = 176

# The kind-L class (pair orbit 0): A_u = e_4 -> e_2, e_5 -> e_1, e_6 -> e_0, R = span(e_0, e_1, e_2).
L_AU = 266304
L_R = (4, 2, 1)
LBITS = 18
L_GATE = {"order": 12288, "valid": 344 * 512 - 2, "orbits": 308,
          "by_rank": {"0": 51, "1": 174, "2": 83}}

# (B5): the two open classes of batch c with d = 1 (A_u from m57.BATCH_C), and the two d = 3 classes
# to split, with m55's counts (out/m55_o002_c000.json, m55_o001_c000.json).
B5_XOR = ("r3b_t7_B5_o009_c009", "r3b_t7_B5_o016_c024")
SPLIT = {"r3b_t7_B5_o002_c000": {"orbits": 421, "by_rank": {"0": 64, "1": 257, "2": 100}},
         "r3b_t7_B5_o001_c000": {"orbits": 445, "by_rank": {"0": 67, "1": 268, "2": 110}}}
REPS_FILE = "m59_reps.json"


def mask_of(cols):
    """The t^2-bit mask (entry (r, c) at bit 7 r + c) of a matrix given by its columns."""
    return sum(((cols[c] >> r) & 1) << (T * r + c) for c in range(T) for r in range(T))


# ---------- the kind-L count in m42's coordinates ----------

def b6_entry(j, i):
    """(unknown or None, constant) for entry i of g e_j: g e_0 = e_0 and g P inside P, with
    P = span(e_1, ..., e_6); unknowns x_(6 (j - 1) + (i - 1)) for 1 <= i, j <= 6."""
    if j == 0:
        return None, int(i == 0)
    if 1 <= i <= 6:
        return 6 * (j - 1) + (i - 1), 0
    return None, 0


def b6_group_conditions(au):
    """Linear conditions on the 36 unknowns for g A_u = A_u g (as m55.group_conditions)."""
    rows = []
    for j in range(T):
        for k in range(T):
            mask, c = 0, 0
            for jj in range(T):
                if au[j] >> jj & 1:
                    x, cc = b6_entry(jj, k)
                    if x is not None:
                        mask ^= 1 << x
                    c ^= cc
            for i in range(T):
                if au[i] >> k & 1:
                    x, cc = b6_entry(j, i)
                    if x is not None:
                        mask ^= 1 << x
                    c ^= cc
            rows.append((mask, c))
    return rows


def b6_g_of(x):
    return (m55.X0,) + tuple(sum(((x >> (6 * (j - 1) + (i - 1))) & 1) << i for i in range(1, 7))
                             for j in range(1, 7))


def b6_group(au):
    sol = m55.solve_affine(b6_group_conditions(au), 36)
    if sol is None:
        raise SystemExit("no solution: the identity should be one")
    part, basis = sol
    if len(basis) > 20:
        raise SystemExit("solution space too large: %d" % len(basis))
    out = []
    x = part
    for i in range(1 << len(basis)):
        if i:
            x ^= basis[(i & -i).bit_length() - 1]
        g = b6_g_of(x)
        if m55.rank(g) == T:
            out.append(g)
    return out, len(basis)


def check_b6_group(au, grp):
    for g in grp:
        if g[0] != m55.X0 or any(g[j] & 1 for j in range(1, T)):
            return False
        if m55.compose(g, au) != m55.compose(au, g):
            return False
    return len(set(grp)) == len(grp) and m55.IDENT in set(grp)


class LMaps:
    """The maps A with A x0 = 0 and image in R, indexed by 18 bits: bits 3 (j - 1) to 3 (j - 1) + 2
    are the coordinates of A e_j (1 <= j <= 6) in the basis rb of R. The encoding is linear."""

    def __init__(self, rb):
        self.vec = []
        for c in range(8):
            v = 0
            for i in range(3):
                if c >> i & 1:
                    v ^= rb[i]
            self.vec.append(v)
        self.coord = {v: c for c, v in enumerate(self.vec)}

    def cols(self, idx):
        return (0,) + tuple(self.vec[(idx >> (3 * (j - 1))) & 7] for j in range(1, T))

    def index(self, cols):
        if cols[0]:
            raise ValueError("not in the space of maps")
        idx = 0
        for j in range(1, T):
            idx |= self.coord[cols[j]] << (3 * (j - 1))
        return idx

    def rank_x1(self, idx):
        a = self.cols(idx)
        return m55.rank([m55.apply(a, x) for x in X1])


def l_conj(mp, g, ginv, idx):
    a = mp.cols(idx)
    return mp.index(tuple(m55.apply(g, m55.apply(a, ginv[j])) for j in range(T)))


def l_table(mp, g, ginv):
    """A -> g A g^(-1) on all 2^18 indices, from the images of the 18 index bits."""
    imgs = [l_conj(mp, g, ginv, 1 << k) for k in range(LBITS)]
    tab = [0] * (1 << LBITS)
    for x in range(1, 1 << LBITS):
        tab[x] = tab[x & (x - 1)] ^ imgs[(x & -x).bit_length() - 1]
    return tab


def kind_l(rng):
    t0 = time.time()
    au = m55.cols_of(L_AU)
    grp, dim = b6_group(au)
    grp_ok = check_b6_group(au, grp)
    gens = m55.generators(grp, rng)
    mp = LMaps(L_R)
    au_idx = mp.index(au)
    pairs = [(g, m55.inverse(g)) for g in gens]
    tabs = [l_table(mp, g, gi) for g, gi in pairs]
    sample = [rng.randrange(1 << LBITS) for _ in range(300)]
    linear_ok = all(tab[i] == l_conj(mp, g, gi, i)
                    for (g, gi), tab in zip(pairs, tabs) for i in sample)
    n = 1 << LBITS
    rk = [mp.rank_x1(i) for i in range(n)]
    vflag = bytearray(n)
    valid = []
    for i in range(n):
        if rk[i] <= 2 and i != 0 and i != au_idx:
            vflag[i] = 1
            valid.append(i)
    parent = array("i", range(n))

    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    def union(i, j):
        i, j = find(i), find(j)
        if i != j:
            if i < j:
                parent[j] = i
            else:
                parent[i] = j

    closed = True
    for i in valid:
        for tab in tabs:
            j = tab[i]
            if not vflag[j]:
                closed = False
            union(i, j)
        union(i, i ^ au_idx)
    orb = {}
    for i in valid:
        orb.setdefault(find(i), []).append(i)
    by_rank, reps, sizes_ok = {}, [], True
    for root, members in sorted(orb.items()):
        r = rk[root]
        if any(rk[i] != r for i in members) or (2 * len(grp)) % len(members):
            sizes_ok = False
        by_rank[str(r)] = by_rank.get(str(r), 0) + 1
        cols = mp.cols(root)
        reps.append({"index": root, "cols": list(cols), "a1": mask_of(cols), "rank_x1": r,
                     "size": len(members)})
    sizes_ok = sizes_ok and sum(r["size"] for r in reps) == len(valid)
    return {"solution_space_dim": dim, "order": len(grp), "group_checked": grp_ok,
            "generators": len(gens), "linear_ok": linear_ok, "action_closed": closed,
            "valid": len(valid), "orbits": len(orb), "by_rank": by_rank, "sizes_ok": sizes_ok,
            "reps": reps, "seconds": round(time.time() - t0, 1)}


# ---------- admissibility in m57's terms (independent of the index encodings) ----------

def admissible_graph(a1):
    """Adm of Proposition 30 (a) for pair orbit 2 (m58.admissible_graph)."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(GRAPH_R, v) for v in cols) and m.rank_on_x1(a1) <= 2
            and a1 != 0 and a1 != GRAPH_AU)


def admissible_l(a1):
    """Adm of Proposition 30 (a) for pair orbit 0: kills x0, image inside R, rank on X_1 at most 2,
    not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(L_R, v) for v in cols) and m.rank_on_x1(a1) <= 2
            and a1 != 0 and a1 != L_AU)


def admissible_b5(a1, au, rb):
    """Adm of Proposition 32 (a): kills x0, maps H0 = span(e_0, ..., e_5) into R, rank on X_1 at
    most 2, rank at most 3, rank of A + A_u at most 3, not 0, not A_u."""
    cols = [m.column(a1, c) for c in range(T)]
    return (cols[0] == 0 and all(m.in_span(rb, cols[c]) for c in range(1, 6))
            and m.rank_on_x1(a1) <= 2 and sa.rank_f2(m.cols_of(a1, T)) <= 3
            and sa.rank_f2(m.cols_of(a1 ^ au, T)) <= 3 and a1 != 0 and a1 != au)


def distinct_with_au(maps, au):
    return len(set(maps) | {a ^ au for a in maps}) == 2 * len(maps)


# ---------- instances ----------

def graph_spec(k, index, rank_x1, a1):
    return {"name": f"r3g_t7_B6_o002_a{k:03d}", "kind": "main", "t": T, "d": D, "p": 6, "pair": 2,
            "x1": list(X1), "r": list(GRAPH_R), "au": GRAPH_AU, "a1": a1, "rank_x1": rank_x1,
            "m52_index": index}


def l_spec(k, rep):
    return {"name": f"r3l_t7_B6_o000_a{k:03d}", "kind": "main", "t": T, "d": D, "p": 6, "pair": 0,
            "x1": list(X1), "r": list(L_R), "au": L_AU, "a1": rep["a1"],
            "rank_x1": rep["rank_x1"], "m59_index": rep["index"], "size": rep["size"]}


def split_spec(name, k, rep):
    pi, ci = m.pair_cls(name)
    au, x1, rb = m55.CLASSES[name]
    return {"name": f"r3s_t7_B5_o{pi:03d}_c{ci:03d}_a{k:03d}", "kind": "main", "t": T, "d": D,
            "p": 5, "pair": pi, "cls": ci, "x1": list(x1), "r": list(rb), "au": au,
            "a1": rep["a1"], "rank_x1": rep["rank_x1"], "m55_index": rep["index"],
            "size": rep["size"], "parent": name}


def plan(group, reps):
    """[(spec, arm, cap seconds, condition, named)]; condition "open" runs the entry only if the
    same instance is still undecided; a named entry gets its full cap, the others a share of what
    is left."""
    out = []
    if group == "a":
        for row in GRAPH_OPEN:
            sp = graph_spec(*row)
            out += [(sp, "cadical", 900.0, None, True), (dict(sp), "xor", 900.0, "open", True)]
        return out + [(l_spec(k, r), "cadical", 25.0, None, False) for k, r in enumerate(reps["L"])]
    out = [(m.b5_spec(n, m.BATCH_C[n]), "xor", 300.0, None, True) for n in B5_XOR]
    for name in SPLIT:
        out += [(split_spec(name, k, r), "cadical", 20.0, None, False)
                for k, r in enumerate(reps[name])]
    return out


def load_reps(out_dir):
    with open(os.path.join(out_dir, REPS_FILE)) as f:
        return json.load(f)


# ---------- check ----------

def check(out_dir):
    start = time.time()
    st57 = m.check(out_dir)
    graded = {"m57_" + k: v for k, v in st57["graded"].items()}
    st = {"m57": {k: v for k, v in st57.items() if k != "graded"}}
    graded["graph_open"] = all(admissible_graph(a1) and m.rank_on_x1(a1) == rk
                               for _, _, rk, a1 in GRAPH_OPEN)
    graded["b5_xor_d1"] = all(n in m.BATCH_C and m.meet_d(m.b5_spec(n, m.BATCH_C[n])) == 1
                              for n in B5_XOR)
    # Kind L.
    graded["l_au"] = (m.kernel(L_AU, T) == X1 and m.column_space(L_AU, T) == L_R
                      and m.dim_meet(X1, L_R) == 3 and m.in_span(L_R, 1))
    lres = kind_l(random.Random(59))
    st["kind_l"] = {k: v for k, v in lres.items() if k != "reps"}
    graded["l_group"] = lres["group_checked"] and lres["order"] == L_GATE["order"]
    graded["l_valid"] = (lres["valid"] == L_GATE["valid"] and lres["action_closed"]
                         and lres["linear_ok"])
    graded["l_orbits"] = (lres["orbits"] == L_GATE["orbits"] and lres["by_rank"] == L_GATE["by_rank"]
                          and lres["sizes_ok"])
    lreps = lres["reps"]
    graded["l_reps"] = (all(admissible_l(r["a1"]) and m.rank_on_x1(r["a1"]) == r["rank_x1"]
                            for r in lreps)
                        and distinct_with_au([r["a1"] for r in lreps], L_AU))
    reps = {"L": lreps}
    # (B5) splits, by m55.py.
    rng, cache, st["split"] = random.Random(55), {}, {}
    for name, gate in SPLIT.items():
        tag = name[10:]
        r = m55.run_class(name, rng, cache)
        s = r["structure"]
        st["split"][tag] = {k: v for k, v in r.items() if k != "reps"}
        graded["split_" + tag] = (s["rank_au"] == 3 and s["ker_is_x1"] and s["im_is_r"] and s["d3"]
                                  and r["group_checked"] and r["order"] == r["order_hand"]
                                  and r["valid"] == r["valid_hand"] and r["action_closed"]
                                  and r["fast_matches_slow"] and r["linear_ok"] and r["sizes_ok"]
                                  and r["orbits"] == gate["orbits"]
                                  and r["orbits_by_rank_x1"] == gate["by_rank"])
        au, _, rb = m55.CLASSES[name]
        out = []
        for rep in r["reps"]:
            out.append({"index": rep["index"], "cols": rep["cols"], "a1": mask_of(rep["cols"]),
                        "rank_x1": rep["rank_x1"], "size": rep["size"]})
        graded["split_reps_" + tag] = (
            all(m55.cols_of(x["a1"]) == tuple(x["cols"]) and admissible_b5(x["a1"], au, rb)
                and m.rank_on_x1(x["a1"]) == x["rank_x1"] for x in out)
            and distinct_with_au([x["a1"] for x in out], au))
        reps[name] = out
    # Hints and units of one instance of each kind (CNF arm; m57's check covers the XOR arm).
    probes = {}
    first = next(iter(SPLIT))
    for key, sp, hints in (("L", l_spec(0, lreps[0]) if lreps else None, m.HAND_HINTS["B6"]),
                           ("split", split_spec(first, 0, reps[first][0]) if reps[first] else None,
                            m.HAND_HINTS["B5"])):
        if sp is None:
            graded["probe_" + key] = False
            continue
        c, _, h, u = m.build(sp, "cadical")
        probes[key] = [c.nv, len(c.clauses), h, u]
        graded["probe_" + key] = h == hints and u == T * T and m.units_consistent(c)
    st["probes"] = probes
    with open(os.path.join(out_dir, REPS_FILE), "w") as f:
        json.dump(reps, f)
    st["graded"] = graded
    st["seconds"] = round(time.time() - start, 1)
    return st


# ---------- solving ----------

def run_solve(group, group_seconds, out_dir):
    start = time.time()
    with open(os.path.join(out_dir, "check.json")) as f:
        if not all(json.load(f)["graded"].values()):
            raise SystemExit("check failed: nothing solved")
    entries = plan(group, load_reps(out_dir))
    shared = sum(1 for e in entries if not e[4])
    counts, decided, done_shared = {}, set(), 0
    for spec, arm, cap, cond, named in entries:
        if cond == "open" and spec["name"] in decided:
            continue
        left = group_seconds - (time.time() - start)
        if left < 5:
            res = dict(spec, arm=arm, status="SKIPPED")
            with open(os.path.join(out_dir, m.tag_of(spec, arm) + ".json"), "w") as f:
                json.dump(res, f, indent=1)
        else:
            if named:
                budget = min(cap, left)
            else:
                budget = min(cap, max(min(MIN_BUDGET, left), left / (shared - done_shared)))
            res = m.solve_one(spec, arm, budget, out_dir)
        if not named:
            done_shared += 1
        if res["status"] in ("SAT", "UNSAT"):
            decided.add(spec["name"])
        key = f"{arm}_{res['status']}"
        counts[key] = counts.get(key, 0) + 1
    print(f"SUMMARY solve group {group} {json.dumps(counts, sort_keys=True)}", flush=True)


# ---------- grading (pre-registered in m59-predictions.md) ----------

def grade(group, out_dir):
    graded, ungraded = {}, {}
    try:
        with open(os.path.join(out_dir, "check.json")) as f:
            for key, ok in json.load(f)["graded"].items():
                graded["check_" + key] = bool(ok)
    except (OSError, ValueError, KeyError):
        ungraded["check"] = "missing"
    try:
        reps = load_reps(out_dir)
    except (OSError, ValueError):
        ungraded["reps"] = "missing"
        return {"group": group, "graded": graded, "ungraded": ungraded, "rows": {}, "by": {},
                "any_sat_7": False}
    rows, by_key, status = {}, {}, {}
    for spec, arm, _, _, named in plan(group, reps):
        tag = m.tag_of(spec, arm)
        path = os.path.join(out_dir, tag + ".json")
        if not os.path.exists(path):
            continue
        with open(path) as f:
            r = json.load(f)
        s = r.get("status")
        rows[tag] = [s, r.get("wall_seconds")]
        if s in ("SAT", "UNSAT"):
            status[spec["name"]] = s
        else:
            status.setdefault(spec["name"], s)
        if s == "SAT":
            graded[tag + "_verified"] = bool(r.get("verified"))
            graded[tag + "_ranks"] = r.get("max_rank", 99) <= 4 and r.get("rank_u") == 3
        if named:
            continue
        key = (f"rank_x1_{spec['rank_x1']}" if group == "a"
               else f"{spec['parent'][10:]}_rank_x1_{spec['rank_x1']}")
        by_key.setdefault(key, {})
        by_key[key][s] = by_key[key].get(s, 0) + 1
    out = {"group": group, "graded": graded, "ungraded": ungraded, "rows": rows, "by": by_key,
           "any_sat_7": any(s == "SAT" for s, _ in rows.values())}
    if group == "a":
        names = [graph_spec(*row)["name"] for row in GRAPH_OPEN]
        out["graph_open"] = {n: status.get(n) for n in names}
        out["graph_unsat_of_178"] = GRAPH_UNSAT_BEFORE + sum(status.get(n) == "UNSAT" for n in names)
        out["kind_graph_empty"] = out["graph_unsat_of_178"] == 178
        lnames = [l_spec(k, r)["name"] for k, r in enumerate(reps["L"])]
        out["l_unsat"] = sum(status.get(n) == "UNSAT" for n in lnames)
        out["l_total"] = len(lnames)
        out["l_open"] = [n for n in lnames if status.get(n) != "UNSAT"]
        out["kind_l_empty"] = out["l_total"] == L_GATE["orbits"] and out["l_unsat"] == out["l_total"]
    else:
        out["b5_xor"] = {n: status.get(n) for n in B5_XOR}
        out["split"] = {}
        closed = [n for n in B5_XOR if status.get(n) == "UNSAT"]
        for name in SPLIT:
            snames = [split_spec(name, k, r)["name"] for k, r in enumerate(reps[name])]
            unsat = sum(status.get(n) == "UNSAT" for n in snames)
            out["split"][name] = {"unsat": unsat, "total": len(snames),
                                  "open": [n for n in snames if status.get(n) != "UNSAT"],
                                  "empty": len(snames) == SPLIT[name]["orbits"] and unsat == len(snames)}
            if out["split"][name]["empty"]:
                closed.append(name)
        out["b5_closed"] = closed
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--part", choices=["check", "solve", "grade"], default="check")
    ap.add_argument("--group", choices=["a", "b"], default="a")
    ap.add_argument("--group-minutes", type=float, default=150.0)
    ap.add_argument("--out-dir", default=".")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    if args.part == "solve":
        run_solve(args.group, args.group_minutes * 60, args.out_dir)
    elif args.part == "grade":
        out = grade(args.group, args.out_dir)
        print(f"grade: {json.dumps(out, sort_keys=True)}", flush=True)
        print(f"SUMMARY grade group {args.group} all_match {all(out['graded'].values())} "
              f"graded {len(out['graded'])} ungraded {len(out['ungraded'])} "
              f"any_sat_7 {out['any_sat_7']} by {json.dumps(out['by'], sort_keys=True)} "
              f"graph {out.get('graph_open')} l_unsat {out.get('l_unsat')} "
              f"b5_closed {out.get('b5_closed')}", flush=True)
        with open(os.path.join(args.out_dir, "grade.json"), "w") as f:
            json.dump(out, f, indent=1)
    else:
        st = check(args.out_dir)
        print(f"check: {json.dumps(st, sort_keys=True)}", flush=True)
        print(f"SUMMARY check all_match {all(st['graded'].values())}", flush=True)
        with open(os.path.join(args.out_dir, "check.json"), "w") as f:
            json.dump(st, f, indent=1)


if __name__ == "__main__":
    main()
