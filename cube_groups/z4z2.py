"""Check Theorem 39 (robust-cubes-v5t) on explicit 2-groups.

Setting: L a finite 2-group whose involutions are all central, A <| L self-centralising with
A ~ Z_4^a x Z_2^b, Omega = Omega_1(A) (rank k = a + b), 2A ~ F_2^a, H = L/A ~ F_2^n.
Each h in H acts as x -> x + delta_h(xbar), delta_h : A/Omega = F_2^a -> Omega = F_2^k, and
delta_h = [P_h ; Q_h] (P: the 2A rows, Q: the Omega/2A rows). H_0 = {h : Q_h = 0}.

Theorem 39: with s = dim span sigma(H_0),
    dim H_0 <= a + s + 2b,   rank Q <= b (a - s),   so  n <= a + 2b + ab - s (b - 1).
For b = 1 this gives n <= 2a + 2, so |L| <= 2^(4a + 3) < |Omega|^4 (and e <= 3 always).
Proof on H_0: rho(h) = g^2 mod 2A is a well-defined quadratic map there, and
    F(h) = det(I + P_h + D(sigma(h))) * prod_j (1 + rho_2,j(h))
is the indicator of h = 0, with degree <= a + s + 2b in a basis adapted to S_0 = span sigma(H_0).
Off H_0: Q_(h') sigma(h) = Q_h beta(h, h') (Lemma 22(c), Q rows) kills S_0.

This script rebuilds every object from each group's multiplication and checks each step.
Control: (Z_4^2 x| Z_2) x Z_2 has a non-central involution, and F is NOT the indicator there.

By MV2 of Munim, Inc. Licence: Apache-2.0.
"""

import argparse
import itertools
import json
import os
import random


# ---------- groups: (elements, mul, order-4 generators of A, order-2 generators of A) ----------

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
    return units, quat_mul, [(0, 1, 0, 0)], []


def p32():
    """b^x g^y with g^2 = a, g b g^-1 = b a^2 (order 32, exponent 8); A = <b, a> ~ Z_4^2."""
    elems = [(x, y) for x in range(4) for y in range(8)]

    def mul(p, q):
        return ((p[0] + q[0]) % 4, (p[1] + q[1] + 4 * q[0] * p[1]) % 8)
    return elems, mul, [(1, 0), (0, 2)], []


def z4z4(swap):
    """Z_4 x| Z_4 = <a, g | g a g^-1 = a^-1>, element a^u g^v = (u, v).

    swap False: A = <a> x <g^2> (Q = 0). swap True: A = <g> x <a^2>, on which a acts by
    g -> g a^2, so Q != 0."""
    elems = [(u, v) for u in range(4) for v in range(4)]

    def mul(p, q):
        return ((p[0] + (q[0] if p[1] % 2 == 0 else -q[0])) % 4, (p[1] + q[1]) % 4)
    if swap:
        return elems, mul, [(0, 1)], [(2, 0)]
    return elems, mul, [(1, 0)], [(0, 2)]


def z2():
    return [0, 1], (lambda p, q: p ^ q), [], [1]


def z4sq_z2():
    """Control: Z_4^2 x| Z_2, the involution acting as I + 2M, M = [[0,1],[1,1]]."""
    elems = [(u, v, e) for u in range(4) for v in range(4) for e in range(2)]

    def phi(u, v):
        return (u + 2 * v) % 4, (v + 2 * (u + v)) % 4

    def mul(p, q):
        u, v = (q[0], q[1]) if p[2] == 0 else phi(q[0], q[1])
        return ((p[0] + u) % 4, (p[1] + v) % 4, p[2] ^ q[2])
    return elems, mul, [(1, 0, 0), (0, 1, 0)], []


def identity_of(elems, mul):
    return next(e for e in elems if all(mul(e, x) == x for x in elems))


def product(G1, G2):
    E1, m1, F1, T1 = G1
    E2, m2, F2, T2 = G2
    e1, e2 = identity_of(E1, m1), identity_of(E2, m2)
    elems = [(x, y) for x in E1 for y in E2]

    def mul(p, q):
        return (m1(p[0], q[0]), m2(p[1], q[1]))
    return (elems, mul, [(g, e2) for g in F1] + [(e1, g) for g in F2],
            [(g, e2) for g in T1] + [(e1, g) for g in T2])


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


def inverse2(M):
    k = len(M)
    R = [list(M[r]) + [int(r == i) for i in range(k)] for r in range(k)]
    for c in range(k):
        p = next(r for r in range(c, k) if R[r][c])
        R[c], R[p] = R[p], R[c]
        for r in range(k):
            if r != c and R[r][c]:
                R[r] = [x ^ y for x, y in zip(R[r], R[c])]
    return tuple(tuple(R[r][k:]) for r in range(k))


def matmul(X, Y):
    return tuple(tuple(sum(X[r][j] * Y[j][c] for j in range(len(Y))) % 2 for c in range(len(Y[0])))
                 for r in range(len(X)))


def matvec(M, v):
    return tuple(sum(M[r][c] * v[c] for c in range(len(v))) % 2 for r in range(len(M)))


def vadd(u, v):
    return tuple((x + y) % 2 for x, y in zip(u, v))


def span(vecs, dim):
    out = {tuple([0] * dim)}
    for v in vecs:
        out |= {vadd(w, v) for w in out}
    return out


def greedy_basis(vecs, dim):
    basis, spanned = [], {tuple([0] * dim)}
    for v in vecs:
        if v not in spanned:
            basis.append(v)
            spanned |= {vadd(w, v) for w in spanned}
    return basis


def anf_degree(values, n):
    """Degree of the multilinear F_2 polynomial of a function on F_2^n (-1 for zero)."""
    f = list(values)
    for i in range(n):
        for x in range(1 << n):
            if (x >> i) & 1:
                f[x] ^= f[x ^ (1 << i)]
    return max((bin(x).count("1") for x in range(1 << n) if f[x]), default=-1)


def log2_exact(m):
    return m.bit_length() - 1 if m > 0 and m & (m - 1) == 0 else None


# ---------- analysis ----------

def analyze(elems, mul, A4, A2, assoc_full=64, samples=20000, seed=1):
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
    a, b = len(A4), len(A2)
    k = a + b

    def power(g, m):
        out = e
        for _ in range(m):
            out = mul(out, g)
        return out

    def order(g):
        m, x = 1, g
        while x != e:
            x, m = mul(x, g), m + 1
        return m
    gens = A4 + A2
    coord = {}
    for xs in itertools.product(*([range(4)] * a + [range(2)] * b)):
        g = e
        for gen, m in zip(gens, xs):
            g = mul(g, power(gen, m))
        coord[g] = xs
    A_ok = (len(coord) == 4 ** a * 2 ** b
            and all(power(g, 4) == e and power(g, 2) != e for g in A4)
            and all(g != e and mul(g, g) == e for g in A2)
            and all(mul(x, y) == mul(y, x) for x in gens for y in gens))
    normal = all(mul(mul(g, x), inv[g]) in coord for g in elems for x in gens)
    cent = {g for g in elems if all(mul(g, x) == mul(x, g) for x in gens)}
    self_centralising = cent == set(coord)
    centre = {z for z in elems if all(mul(z, g) == mul(g, z) for g in elems)}
    invols = [x for x in elems if x != e and mul(x, x) == e]
    all_central = all(x in centre for x in invols)
    omega_set = {x for x, c in coord.items() if all(v % 2 == 0 for v in c[:a])}
    omega_ok = (set(invols) | {e}) == omega_set
    exponent = max(order(g) for g in elems).bit_length() - 1

    def om(c):                      # Omega element -> F_2^k (2A part, then the Z_2 part)
        return tuple(v // 2 for v in c[:a]) + tuple(c[a:])

    coset_of, reps, members = {}, [], []
    for g in elems:
        if g not in coset_of:
            c = len(reps)
            reps.append(g)
            members.append([])
            for x in coord:
                y = mul(g, x)
                coset_of[y] = c
                members[c].append(y)
    nH = len(reps)
    n = log2_exact(nH)
    squares_in_A = all(mul(g, g) in coord for g in elems)
    ok = {"associative": assoc, "A_shape": A_ok, "normal": normal,
          "self_centralising": self_centralising, "all_involutions_central": all_central,
          "omega1_L_is_omega1_A": omega_ok, "squares_in_A": squares_in_A, "index_power_of_2": n is not None}
    res = {"order": N, "a": a, "b": b, "k": k, "n": n, "exponent_log2": exponent}
    if not (squares_in_A and n is not None and A_ok):
        res.update(ok)
        res["theorem39_consistent"] = False
        return res

    # delta_h : columns = images of the order-4 generators, as F_2^k vectors; Z_2 gens fixed
    D, act_ok = [], True
    for g in reps:
        cols = []
        for x in A4:
            c = coord.get(mul(mul(mul(g, x), inv[g]), inv[x]))
            if c is None or any(v % 2 for v in c[:a]):
                act_ok = False
                cols.append((0,) * k)
            else:
                cols.append(om(c))
        act_ok &= all(mul(mul(g, x), inv[g]) == x for x in A2)
        D.append(tuple(tuple(cols[i][r] for i in range(a)) for r in range(k)))

    def madd(X, Y):
        return tuple(tuple((p + q) % 2 for p, q in zip(rx, ry)) for rx, ry in zip(X, Y))
    zero_ka = tuple(tuple([0] * a) for _ in range(k))
    additive = all(D[coset_of[mul(reps[c1], reps[c2])]] == madd(D[c1], D[c2])
                   for c1 in range(nH) for c2 in range(nH))
    injective = all(D[c] != zero_ka for c in range(1, nH))

    sig = {g: tuple(v % 2 for v in coord[mul(g, g)][:a]) for g in elems}
    sigma = [sig[g] for g in reps]
    sigma_wd = all(sig[g] == sigma[coset_of[g]] for g in elems)

    def J(u):
        return tuple(u) + (0,) * b

    def beta(c1, c2):               # c' = g' g g'^-1 g^-1 mod Omega
        g, h = reps[c1], reps[c2]
        cp = coord.get(mul(mul(mul(h, g), inv[h]), inv[g]))
        return None if cp is None else tuple(v % 2 for v in cp[:a])
    identity_c = True
    for c1 in range(nH):
        for c2 in range(nH):
            bt = beta(c1, c2)
            identity_c &= bt is not None and \
                matvec(D[c2], sigma[c1]) == vadd(J(bt), matvec(D[c1], bt))

    # coordinates on H
    hb = greedy_basis_cosets(reps, coset_of, mul, range(nH))
    elementary = len(hb) == n

    Q = [tuple(D[c][a:]) for c in range(nH)]
    P = [tuple(D[c][:a]) for c in range(nH)]
    zero_ba = tuple(tuple([0] * a) for _ in range(b))
    H0 = [c for c in range(nH) if Q[c] == zero_ba]
    n0 = log2_exact(len(H0))
    rank_Q = None if n0 is None else n - n0

    # rho on H_0: g^2 mod 2A, as (sigma part, Z_2 part)
    def rho_of(g):
        c = coord[mul(g, g)]
        return tuple(v % 2 for v in c[:a]) + tuple(c[a:])
    rho = {c: rho_of(reps[c]) for c in H0}
    rho_wd = all(rho_of(g) == rho[c] for c in H0 for g in members[c])

    S0 = greedy_basis([sigma[c] for c in H0], a)
    s = len(S0)
    Q_kills_S0 = all(matvec(Q[c], v) == (0,) * b for c in range(nH) for v in S0)

    # basis of F_2^a adapted to S_0: columns S0 + standard vectors; T = B^-1
    std = [tuple(int(i == j) for i in range(a)) for j in range(a)]
    cols = greedy_basis(S0 + std, a)
    if a:
        B = tuple(tuple(cols[j][r] for j in range(a)) for r in range(a))
        T = inverse2(B)
    I_a = tuple(tuple(int(r == i) for i in range(a)) for r in range(a))

    def N_of(c):
        if not a:
            return ()
        Pp = matmul(matmul(T, P[c]), B)
        sp = matvec(T, sigma[c])
        return tuple(tuple((I_a[r][i] + Pp[r][i] + (sp[r] if r == i else 0)) % 2 for i in range(a))
                     for r in range(a))
    Nm = {c: N_of(c) for c in H0}
    F = {c: (det2(Nm[c]) if a else 1) * int(all(v == 0 for v in rho[c][a:])) for c in H0}
    indicator = F[0] == 1 and all(F[c] == 0 for c in H0 if c != 0)

    # degrees in coordinates of H_0
    deg_ok, rho_deg, quad_rows, lin_rows = True, -1, -1, -1
    if n0 is not None:
        b0 = greedy_basis_cosets(reps, coset_of, mul, H0)
        cid0 = []
        for x in range(1 << n0):
            g = e
            for i in range(n0):
                if (x >> i) & 1:
                    g = mul(g, reps[b0[i]])
            cid0.append(coset_of[g])
        deg_ok = len(b0) == n0 and sorted(cid0) == sorted(H0)
        for j in range(k):
            rho_deg = max(rho_deg, anf_degree([rho[c][j] for c in cid0], n0))
        for r in range(a):
            for i in range(a):
                dg = anf_degree([Nm[c][r][i] for c in cid0], n0)
                if r < s:
                    quad_rows = max(quad_rows, dg)
                else:
                    lin_rows = max(lin_rows, dg)
        deg_ok &= rho_deg <= 2 and quad_rows <= 2 and lin_rows <= 1

    bound_n = a + 2 * b + a * b - s * (b - 1)
    res.update(ok)
    res.update({
        "action_ok": act_ok, "delta_additive": additive, "delta_injective": injective,
        "sigma_well_defined": sigma_wd, "identity_c": identity_c, "H_elementary": elementary,
        "n0": n0, "rank_Q": rank_Q, "s": s, "rho_well_defined_on_H0": rho_wd,
        "Q_kills_S0": Q_kills_S0, "F_is_indicator_on_H0": indicator,
        "rho_degree": rho_deg, "N_quadratic_rows_degree": quad_rows, "N_linear_rows_degree": lin_rows,
        "degrees_ok": deg_ok,
        "n0_le_a_s_2b": n0 is not None and n0 <= a + s + 2 * b,
        "rankQ_le_b_a_minus_s": rank_Q is not None and rank_Q <= b * (a - s),
        "n_le_bound": n <= bound_n, "bound_n": bound_n, "n_le_ak": n <= a * k,
        "order_le_omega_pow_e_plus_1": 2 * a + b + n <= (exponent + 1) * k,
    })
    res["theorem39_consistent"] = all(res[key] for key in (
        "associative", "A_shape", "normal", "self_centralising", "all_involutions_central",
        "omega1_L_is_omega1_A", "squares_in_A", "index_power_of_2", "action_ok", "delta_additive",
        "delta_injective", "sigma_well_defined", "identity_c", "H_elementary",
        "rho_well_defined_on_H0", "Q_kills_S0", "F_is_indicator_on_H0", "degrees_ok",
        "n0_le_a_s_2b", "rankQ_le_b_a_minus_s", "n_le_bound", "order_le_omega_pow_e_plus_1"))
    return res


def greedy_basis_cosets(reps, coset_of, mul, ids):
    """A basis (list of coset ids) of the elementary abelian subgroup formed by `ids`."""
    basis, spanned = [], {0}
    for c in ids:
        if c not in spanned:
            basis.append(c)
            spanned |= {coset_of[mul(reps[t], reps[c])] for t in spanned}
    return basis


def groups():
    Q, P, Z = q8(), p32(), z2()
    W0, W1 = z4z4(False), z4z4(True)
    return [
        ("Q8xZ2", product(Q, Z), False),
        ("Z4:Z4, A=<a,g^2>", W0, False),
        ("Z4:Z4, A=<g,a^2>", W1, False),
        ("P32xZ2", product(P, Z), False),
        ("Q8xQ8xZ2", product(product(Q, Q), Z), False),
        ("Q8x(Z4:Z4)'", product(Q, W1), False),
        ("(Z4:Z4)'x(Z4:Z4)'", product(W1, W1), False),
        ("P32x(Z4:Z4)'", product(P, W1), False),
        ("Q8xQ8xQ8xZ2", product(product(product(Q, Q), Q), Z), False),
        ("P32xP32xZ2", product(product(P, P), Z), False),
        ("(Z4^2:Z2)xZ2 control", product(z4sq_z2(), Z), True),
    ]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out-dir", default="out")
    args = ap.parse_args()
    os.makedirs(args.out_dir, exist_ok=True)
    results = {}
    for name, (E, mul, A4, A2), control in groups():
        r = analyze(E, mul, A4, A2)
        r["control"] = control
        results[name] = r
        print(name, json.dumps(r))
    ctrl = results["(Z4^2:Z2)xZ2 control"]
    summary = {
        "groups_consistent": sum(1 for r in results.values()
                                 if not r["control"] and r["theorem39_consistent"]),
        "groups": sum(1 for r in results.values() if not r["control"]),
        "rankQ_positive_groups": sum(1 for r in results.values()
                                     if not r["control"] and (r.get("rank_Q") or 0) > 0),
        "control_indicator_fails_with_noncentral_involution":
            not ctrl["F_is_indicator_on_H0"] and not ctrl["all_involutions_central"],
    }
    print("SUMMARY", json.dumps(summary))
    with open(os.path.join(args.out_dir, "z4z2.json"), "w") as f:
        json.dump({"summary": summary, "groups": results}, f, indent=1)


if __name__ == "__main__":
    main()
