"""Check Theorem 38 (robust-cubes-v5s) on explicit 2-groups.

Theorem 38: if a finite 2-group L whose involutions are all central has a self-centralising
normal subgroup A ~ Z_4^k, then H = L/A is elementary abelian of rank n <= 2k, so |L| <= 2^(4k).
Proof: N_h = I + M_h + D(sigma(h)) is the identity at h = 0 and singular for every h != 0
(sigma(h) = 0: I + M_h is singular by Lemma 22(d); sigma(h) = s != 0: N_h s = s + M_h s + s = 0).
Its entries have degree <= 2 in the coordinates of h, so det N_h = delta_0 has degree n <= 2k.

This script builds (M_h, sigma) from each group's multiplication and checks every step:
Lemma 22 (a), (b), (d), M_h sigma(h) = 0, det N_h = delta_0, and the algebraic degrees.
Controls: Z_4^2 x| Z_2 with an irreducible M (non-central involution, det identity fails) and
D_8 (non-central involution, but I + M_h is still singular, so the identity holds).

By MV2 of Munim, Inc. Licence: Apache-2.0.
"""

import argparse
import itertools
import json
import os
import random


# ---------- groups: (elements, mul, generators of A) ----------

def quat_mul(p, q):
    a1, b1, c1, d1 = p
    a2, b2, c2, d2 = q
    return (a1 * a2 - b1 * b2 - c1 * c2 - d1 * d2,
            a1 * b2 + b1 * a2 + c1 * d2 - d1 * c2,
            a1 * c2 - b1 * d2 + c1 * a2 + d1 * b2,
            a1 * d2 + b1 * c2 - c1 * b2 + d1 * a2)


def q8():
    units = []
    for i in range(4):
        for s in (1, -1):
            v = [0, 0, 0, 0]
            v[i] = s
            units.append(tuple(v))
    return units, quat_mul, [(0, 1, 0, 0)]


def p32():
    """b^x g^y with g^2 = a, g b g^-1 = b a^2 (order 32, exponent 8); A = <b, a>."""
    elems = [(x, y) for x in range(4) for y in range(8)]

    def mul(p, q):
        return ((p[0] + q[0]) % 4, (p[1] + q[1] + 4 * q[0] * p[1]) % 8)
    return elems, mul, [(1, 0), (0, 2)]


def z4sq_z2():
    """Control: Z_4^2 x| Z_2, the involution acting as I + 2M, M = [[0,1],[1,1]]."""
    elems = [(u, v, e) for u in range(4) for v in range(4) for e in range(2)]

    def phi(u, v):
        return (u + 2 * v) % 4, (v + 2 * (u + v)) % 4

    def mul(p, q):
        u, v = (q[0], q[1]) if p[2] == 0 else phi(q[0], q[1])
        return ((p[0] + u) % 4, (p[1] + v) % 4, p[2] ^ q[2])
    return elems, mul, [(1, 0, 0), (0, 1, 0)]


def d8():
    """Control: D_8 with A = <r>."""
    elems = [(r, e) for r in range(4) for e in range(2)]

    def mul(p, q):
        return ((p[0] + (q[0] if p[1] == 0 else -q[0])) % 4, p[1] ^ q[1])
    return elems, mul, [(1, 0)]


def identity_of(elems, mul):
    return next(e for e in elems if all(mul(e, x) == x for x in elems))


def product(G1, G2):
    E1, m1, A1 = G1
    E2, m2, A2 = G2
    e1, e2 = identity_of(E1, m1), identity_of(E2, m2)
    elems = [(x, y) for x in E1 for y in E2]

    def mul(p, q):
        return (m1(p[0], q[0]), m2(p[1], q[1]))
    return elems, mul, [(a, e2) for a in A1] + [(e1, a) for a in A2]


# ---------- linear algebra over F_2 ----------

def det2(M):
    R = [list(r) for r in M]
    k = len(R)
    for c in range(k):
        p = next((r for r in range(c, k) if R[r][c]), None)
        if p is None:
            return 0
        R[c], R[p] = R[p], R[c]
        for r in range(c + 1, k):
            if R[r][c]:
                R[r] = [x ^ y for x, y in zip(R[r], R[c])]
    return 1


def matvec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(len(v))) % 2 for r in range(len(M)))


def span(cols, k):
    out = {tuple([0] * k)}
    for c in cols:
        out |= {tuple((x + y) % 2 for x, y in zip(v, c)) for v in out}
    return out


def anf_degree(values, n):
    """Degree of the multilinear F_2 polynomial of a function on F_2^n (-1 for zero)."""
    f = list(values)
    for i in range(n):
        for x in range(1 << n):
            if (x >> i) & 1:
                f[x] ^= f[x ^ (1 << i)]
    return max((bin(x).count("1") for x in range(1 << n) if f[x]), default=-1)


# ---------- analysis ----------

def analyze(elems, mul, Agens, assoc_full=64, samples=20000, seed=1):
    e = identity_of(elems, mul)
    elems = [e] + [x for x in elems if x != e]
    N = len(elems)
    rng = random.Random(seed)
    if N <= assoc_full:
        triples = itertools.product(elems, repeat=3)
    else:
        triples = ((rng.choice(elems), rng.choice(elems), rng.choice(elems)) for _ in range(samples))
    assoc = all(mul(mul(x, y), z) == mul(x, mul(y, z)) for x, y, z in triples)
    inv = {}
    for x in elems:
        if x not in inv:
            y = next(y for y in elems if mul(x, y) == e)
            inv[x], inv[y] = y, x
    k = len(Agens)

    def power(g, m):
        a = e
        for _ in range(m):
            a = mul(a, g)
        return a
    coord = {}
    for xs in itertools.product(range(4), repeat=k):
        a = e
        for g, m in zip(Agens, xs):
            a = mul(a, power(g, m))
        coord[a] = xs
    A_ok = (len(coord) == 4 ** k
            and all(power(g, 4) == e and power(g, 2) != e for g in Agens)
            and all(mul(a, b) == mul(b, a) for a in Agens for b in Agens))
    normal = all(mul(mul(g, a), inv[g]) in coord for g in elems for a in Agens)
    cent = {g for g in elems if all(mul(g, a) == mul(a, g) for a in Agens)}
    self_centralising = cent == set(coord)
    centre = {z for z in elems if all(mul(z, g) == mul(g, z) for g in elems)}
    invols = [x for x in elems if x != e and mul(x, x) == e]
    all_central = all(x in centre for x in invols)
    twoA = {a for a in coord if all(c % 2 == 0 for c in coord[a])}
    omega_is_2A = (set(invols) | {e}) == twoA

    coset_of, reps = {}, []
    for g in elems:
        if g not in coset_of:
            c = len(reps)
            reps.append(g)
            for a in coord:
                coset_of[mul(g, a)] = c
    nH = len(reps)
    n = nH.bit_length() - 1
    squares_in_A = all(mul(g, g) in coord for g in elems)
    sig_by_elem = {g: tuple(c % 2 for c in coord[mul(g, g)]) for g in elems} if squares_in_A else {}
    sigma = [sig_by_elem.get(g) for g in reps]
    sigma_well_defined = squares_in_A and all(sig_by_elem[g] == sigma[coset_of[g]] for g in elems)
    M, act_ok = [], True
    for g in reps:
        cols = []
        for a in Agens:
            c = coord.get(mul(mul(mul(g, a), inv[g]), inv[a]))
            if c is None or any(x % 2 for x in c):
                act_ok = False
                c = (0,) * k
            cols.append(tuple((x // 2) % 2 for x in c))
        M.append(tuple(tuple(cols[i][r] for i in range(k)) for r in range(k)))
    additive = all(
        M[coset_of[mul(reps[c1], reps[c2])]] == tuple(
            tuple((M[c1][r][i] + M[c2][r][i]) % 2 for i in range(k)) for r in range(k))
        for c1 in range(nH) for c2 in range(nH))
    zero = tuple(tuple([0] * k) for _ in range(k))
    injective = all(M[c] != zero for c in range(1, nH))
    I = tuple(tuple(int(r == i) for i in range(k)) for r in range(k))

    def add(X, Y):
        return tuple(tuple((X[r][i] + Y[r][i]) % 2 for i in range(k)) for r in range(k))

    def diag(s):
        return tuple(tuple(s[r] if r == i else 0 for i in range(k)) for r in range(k))
    zero_vec = (0,) * k
    m_sigma_zero = squares_in_A and all(matvec(M[c], sigma[c]) == zero_vec for c in range(nH))
    Nmat = [add(add(I, M[c]), diag(sigma[c])) if squares_in_A else I for c in range(nH)]
    dets = [det2(X) for X in Nmat]
    det_is_delta = dets[0] == 1 and all(d == 0 for d in dets[1:])
    # Lemma 22(d): coset c != 0 has an involution iff sigma = 0 and g^2 = 2t with t in Im(I + M)
    d_criterion = True
    sigma0_singular = True
    for c in range(1, nH):
        has_inv = any(x in coset_of and coset_of[x] == c for x in invols)
        if squares_in_A and sigma[c] == zero_vec:
            t = tuple((x // 2) % 2 for x in coord[mul(reps[c], reps[c])])
            IM = add(I, M[c])
            pred = t in span([tuple(IM[r][i] for r in range(k)) for i in range(k)], k)
            sigma0_singular &= det2(IM) == 0 or has_inv
        else:
            pred = False
        d_criterion &= pred == has_inv
    # degrees in coordinates of H
    basis, spanned = [], {0}
    for c in range(nH):
        if c not in spanned and len(basis) < n:
            basis.append(reps[c])
            new = set()
            for s in spanned:
                new.add(coset_of[mul(reps[s], reps[c])])
            spanned |= new
    elementary = squares_in_A and len(spanned) == nH and len(basis) == n
    entry_deg, det_deg = -1, None
    if elementary:
        cid = []
        for x in range(1 << n):
            g = e
            for i in range(n):
                if (x >> i) & 1:
                    g = mul(g, basis[i])
            cid.append(coset_of[g])
        for r in range(k):
            for i in range(k):
                entry_deg = max(entry_deg, anf_degree([Nmat[c][r][i] for c in cid], n))
        det_deg = anf_degree([dets[c] for c in cid], n)
    return {
        "order": N, "k": k, "n": n, "associative": assoc, "A_is_Z4k": A_ok, "normal": normal,
        "self_centralising": self_centralising, "all_involutions_central": all_central,
        "omega_is_2A": omega_is_2A, "H_elementary": elementary, "action_I_plus_2M": act_ok,
        "M_additive": additive, "M_injective": injective, "sigma_well_defined": sigma_well_defined,
        "sigma_nonzero_cosets": sum(1 for s in sigma if s and any(s)),
        "M_sigma_zero": m_sigma_zero, "lemma22d_criterion": d_criterion,
        "sigma0_I_plus_M_singular_or_involution": sigma0_singular,
        "det_is_delta0": det_is_delta, "entry_degree": entry_deg, "det_degree": det_deg,
        "n_le_2k": n <= 2 * k,
    }


def groups():
    Q, P = q8(), p32()
    return [
        ("Q8", Q, False), ("Q8xQ8", product(Q, Q), False), ("P32", P, False),
        ("Q8xQ8xQ8", product(product(Q, Q), Q), False), ("Q8xP32", product(Q, P), False),
        ("P32xP32", product(P, P), False),
        ("Z4^2:Z2 control", z4sq_z2(), True), ("D8 control", d8(), True),
    ]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    results = {}
    for name, (E, mul, A), control in groups():
        r = analyze(E, mul, A)
        r["control"] = control
        if not control:
            r["theorem38_consistent"] = all(r[key] for key in (
                "associative", "A_is_Z4k", "normal", "self_centralising",
                "all_involutions_central", "omega_is_2A", "H_elementary", "action_I_plus_2M",
                "M_additive", "M_injective", "sigma_well_defined", "M_sigma_zero",
                "lemma22d_criterion", "det_is_delta0", "n_le_2k")) and \
                r["entry_degree"] <= 2 and r["det_degree"] == r["n"] <= 2 * r["k"]
        results[name] = r
        print(name, json.dumps(r))
    summary = {
        "groups_consistent": sum(1 for r in results.values() if r.get("theorem38_consistent")),
        "groups": sum(1 for r in results.values() if not r["control"]),
        "control_Z4sq_det_fails": not results["Z4^2:Z2 control"]["det_is_delta0"],
        "control_D8_det_holds_with_noncentral_involution":
            results["D8 control"]["det_is_delta0"]
            and not results["D8 control"]["all_involutions_central"],
    }
    print("SUMMARY", json.dumps(summary))
    with open(os.path.join(args.out_dir, "z4degree.json"), "w") as f:
        json.dump({"summary": summary, "groups": results}, f, indent=1)


if __name__ == "__main__":
    main()
