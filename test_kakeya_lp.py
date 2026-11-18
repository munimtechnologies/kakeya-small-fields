"""Tests for kakeya_lp.py and kakeya_cert_check.py (standard library only).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.

What is checked:
- the F_3 builder reproduces the Katz-Tao gluing (four copies of Z = (X, Y, Y'));
- the independent checker accepts the Katz-Tao proof written as a certificate, with
  bound exactly 6/11, and rejects corrupted versions;
- the LP model built from the Katz-Tao word contains that proof (exact combination of its
  own rows gives 6/11), so the LP optimum for this word is at least 6/11;
- every row of the model holds on exact realisations of the construction for explicit
  Kakeya maps of F_3 (copy identities, equal-law rows, normalisation, the Kakeya
  restriction, closures, sampled Shannon rows).
"""

import math
import random
import unittest
from fractions import Fraction

import kakeya_cert_check as chk
import kakeya_lp as klp

# Coordinates of the Katz-Tao word: a b c e f g (indices 0..5).
A_ = (1, 0, 0, 0, 0, 0)
B_ = (0, 1, 0, 0, 0, 0)
C_ = (0, 0, 1, 0, 0, 0)
E_ = (0, 0, 0, 1, 0, 0)
F_ = (0, 0, 0, 0, 1, 0)
G_ = (0, 0, 0, 0, 0, 1)


def comb(*terms):
    out = [0] * 6
    for c, u in terms:
        for i in range(6):
            out[i] = (out[i] + c * u[i]) % 3
    return tuple(out)


ABE = comb((1, A_), (1, B_), (-1, E_))        # a + b - e
ACE = comb((1, A_), (1, C_), (-1, E_))        # a + c - e
FABE = comb((1, F_), (1, ABE))                # f + a + b - e
Y4 = comb((1, FABE), (-1, G_))                # f + a + b - e - g

EXPECTED_VERTICES = [
    (A_, B_), (A_, C_), (E_, ABE), (E_, ACE), (F_, ABE), (F_, ACE), (G_, Y4), (G_, ACE)]

EXPECTED_ATOMS = [A_, B_, C_, E_, ABE, ACE, F_, G_, Y4,
                  comb((1, A_), (1, B_)), comb((1, A_), (1, C_)), FABE]


def kt_hand_certificate():
    """The Katz-Tao proof (note a180, Lemma 143 applied to a Kakeya pair) as rows."""
    rows = [
        ({"k": "mi", "A": [0, 1, 2], "B": [6], "C": []}, "1"),
        ({"k": "mi", "A": [0, 1, 2, 6], "B": [8], "C": []}, "1"),
        ({"k": "mi", "A": [9], "B": [10], "C": []}, "1"),
        ({"k": "mi", "A": [4], "B": [5], "C": []}, "1"),
        ({"k": "mi", "A": [11], "B": [5], "C": []}, "1"),
        ({"k": "copy", "step": 0}, "3"),
        ({"k": "copy", "step": 1}, "1"),
        ({"k": "copy", "step": 2}, "1"),
        ({"k": "copy", "step": 3}, "1"),
        ({"k": "law", "step": 1, "S": [0, 1, 2]}, "-3"),
        ({"k": "law", "step": 2, "S": [3, 4, 5]}, "-2"),
        ({"k": "law", "step": 3, "S": [6, 4, 5]}, "-1"),
        ({"k": "norm", "v": 0}, "3"),
        ({"k": "norm", "v": 1}, "3"),
        ({"k": "read", "v": 4, "r": "x"}, "-1"),
        ({"k": "read", "v": 6, "r": "y"}, "-1"),
        ({"k": "read", "v": 0, "r": "s"}, "-1"),
        ({"k": "read", "v": 1, "r": "s"}, "-1"),
        ({"k": "read", "v": 2, "r": "y"}, "-1"),
        ({"k": "read", "v": 3, "r": "y"}, "-2"),
        ({"k": "read", "v": 4, "r": "s"}, "-1"),
        ({"k": "read", "v": 0, "r": "x"}, "-3"),
    ]
    return {
        "format": "kakeya-lp-certificate-1",
        "word": klp.KT_WORD,
        "extras": [],
        "uniform": False,
        "atoms": [["a%d" % i, list(f)] for i, f in enumerate(EXPECTED_ATOMS)],
        "claimed_bound": "6/11",
        "rows": [{"d": d, "m": m} for d, m in rows],
    }


class TestAlgebra(unittest.TestCase):
    def test_rref_and_span(self):
        b = klp.rref([(1, 1, 0), (1, 0, 1)])
        self.assertEqual(b, ((1, 0, 1), (0, 1, 2)))
        self.assertTrue(klp.in_span((2, 1, 1), b))       # (a+b) + (a+c)
        self.assertFalse(klp.in_span((2, 1, 0), b))
        self.assertFalse(klp.in_span((1, 0, 0), b))

    def test_decompose(self):
        basis = [(1, 0, 1), (0, 1, 2), (1, 0, 0)]
        lam = klp.decompose((0, 1, 0), basis)
        self.assertEqual(lam, [1, 1, 2])
        self.assertIsNone(klp.decompose((1, 1), [(1, 0)]))

    def test_checker_subspace(self):
        S = chk.Subspace(3)
        S.insert((1, 1, 0))
        S.insert((1, 0, 1))
        self.assertEqual(S.key(), ((1, 0, 1), (0, 1, 2)))
        self.assertTrue(S.has((2, 1, 1)))
        self.assertFalse(S.has((2, 1, 0)))
        self.assertFalse(S.has((0, 0, 1)))


class TestKTWord(unittest.TestCase):
    def test_vertices(self):
        cfg = klp.Config(klp.KT_WORD)
        self.assertEqual(cfg.r, 6)
        got = [(klp.pad(x, 6), klp.pad(y, 6)) for x, y in zip(cfg.vx, cfg.vy)]
        self.assertEqual(got, EXPECTED_VERTICES)
        R, X, Y, _ = chk.rebuild(klp.KT_WORD)
        self.assertEqual(R, 6)
        self.assertEqual(list(zip(X, Y)), EXPECTED_VERTICES)

    def test_atoms(self):
        cfg = klp.Config(klp.KT_WORD)
        forms, _ = klp.build_atoms(cfg)
        self.assertEqual(forms, EXPECTED_ATOMS)
        R, X, Y, steps = chk.rebuild(klp.KT_WORD)
        self.assertEqual(chk.atom_list(R, X, Y, steps, []), EXPECTED_ATOMS)
        extras = [[[0, "x", 1], [6, "y", 2]], [[3, "d", 1]], [[3, "s", 1]]]  # s3 = a+c repeats
        f1, _ = klp.build_atoms(cfg, extras)
        self.assertEqual(f1, chk.atom_list(R, X, Y, steps, extras))
        self.assertEqual(len(f1), 14)

    def test_closure_w_is_everything(self):
        cfg = klp.Config(klp.KT_WORD)
        verts = cfg.vertices()
        w = klp.closure([A_, B_, C_, F_, Y4], verts)
        self.assertEqual(len(w), 6)
        self.assertEqual(len(klp.closure([A_, B_, C_], verts)), 3)
        self.assertEqual(len(klp.closure([ACE, G_], verts)), 2)
        # d of vertex 7 is a+c-e-g; alone it determines the whole vertex (g, a+c-e)
        self.assertEqual(len(klp.closure([comb((1, ACE), (-1, G_))], verts)), 2)
        self.assertEqual(len(klp.closure([comb((1, ACE), (-1, G_))], [])), 1)


class TestCertificates(unittest.TestCase):
    def test_kt_certificate_passes(self):
        self.assertEqual(chk.check(kt_hand_certificate()), Fraction(6, 11))

    def test_corrupted_multiplier_rejected(self):
        cert = kt_hand_certificate()
        cert["rows"][0]["m"] = "2"
        with self.assertRaises(AssertionError):
            chk.check(cert)

    def test_negative_inequality_rejected(self):
        cert = kt_hand_certificate()
        cert["rows"][2]["m"] = "-1"
        with self.assertRaises(AssertionError):
            chk.check(cert)

    def test_wrong_claim_rejected(self):
        cert = kt_hand_certificate()
        cert["claimed_bound"] = "7/11"
        with self.assertRaises(AssertionError):
            chk.check(cert)

    def test_wrong_atoms_rejected(self):
        cert = kt_hand_certificate()
        cert["atoms"][3] = ["bad", [0, 0, 0, 1, 1, 0]]
        with self.assertRaises(AssertionError):
            chk.check(cert)

    def test_unif_needs_flag(self):
        cert = kt_hand_certificate()
        cert["rows"].append({"d": {"k": "unif", "i": 0}, "m": "1"})
        with self.assertRaises(AssertionError):
            chk.check(cert)


def row_lookup(model):
    return {(sense, tuple(sorted(coefs.items())), const): i
            for i, (sense, coefs, const, _) in enumerate(model.rows)}


def norm_terms(terms):
    out = {}
    for var, c in terms:
        if var == 0 or c == 0:
            continue
        out[var] = out.get(var, 0) + c
    return tuple(sorted((k, v) for k, v in out.items() if v))


class TestModelContainsKT(unittest.TestCase):
    def test_kt_from_model_rows(self):
        model = klp.Model(klp.KT_WORD, uniform=False, max_atoms=12)
        self.assertEqual(model.m, 12)
        look = row_lookup(model)
        col = model.colof

        def mask(ids):
            return sum(1 << i for i in ids)

        mults = {}

        def use(sense, terms, const, mu):
            sig = (sense, norm_terms(terms), const)
            if not sig[1] and const == 0:
                return
            self.assertIn(sig, look)
            ri = look[sig]
            mults[ri] = mults.get(ri, Fraction(0)) + Fraction(mu)

        def sub(i, j, K):
            k = mask(K)
            use("ge", [(col[k | (1 << i)], 1), (col[k | (1 << j)], 1),
                       (col[k | (1 << i) | (1 << j)], -1), (col[k], -1)], 0, 1)

        for i, j, K in [(0, 6, []), (1, 6, [0]), (2, 6, [0, 1]),
                        (0, 8, []), (1, 8, [0]), (2, 8, [0, 1]), (6, 8, [0, 1, 2]),
                        (9, 10, []), (4, 5, []), (5, 11, [])]:
            sub(i, j, K)
        copy_idx = {r[3][1]: i for i, r in enumerate(model.rows) if r[3][0] == "copy"}
        for s, mu in ((0, 3), (1, 1), (2, 1), (3, 1)):
            mults[copy_idx[s]] = Fraction(mu)
        for S, T, mu in (([0, 1, 2], [3, 4, 5], -3), ([3, 4, 5], [6, 4, 5], -2),
                         ([4, 5, 6], [8, 5, 7], -1)):
            use("eq", [(col[mask(S)], 1), (col[mask(T)], -1)], 0, mu)
        for v in (0, 1):
            use("eq", [(col[mask([0, 1] if v == 0 else [0, 2])], 1)], -1, 3)
        for atom, mu in ((6, -1), (8, -1), (9, -1), (10, -1), (4, -1), (5, -2), (11, -1),
                         (0, -3)):
            use("eq", [(col[1 << atom], 1), (model.t, -1)], 0, mu)
        ok, bound, info = klp.combine(model, mults)
        self.assertTrue(ok, info)
        self.assertEqual(bound, Fraction(6, 11))
        cert = klp.export_certificate(model, bound, mults)
        self.assertEqual(chk.check(cert), Fraction(6, 11))


class TestRowsHoldOnRealMaps(unittest.TestCase):
    """Every row must hold for genuine Kakeya maps of F_3 (k = 1, D uniform on F_3)."""

    def test_rows(self):
        extras = [[[0, "x", 1], [6, "y", 2]]]
        model = klp.Model(klp.KT_WORD, extras=extras, uniform=True, max_atoms=13,
                          elemental=False)
        self.assertEqual(model.m, 13)
        rng = random.Random(7)
        for pmap in ([0, 1, 1], [0, 0, 1]):
            law = klp.realize(model.cfg, pmap)
            self.assertEqual(sum(law.values()), 1)
            cache = {}

            def H(var):
                if var == 0:
                    return 0.0
                if var not in cache:
                    cache[var] = klp.entropy_of_key(law, model.keys[var])
                return cache[var]

            root = {r: klp.entropy_of_key(law, [model.cfg.reading(0, r)])
                    for r in ("x", "y", "s")}
            if pmap == [0, 1, 1]:
                frame = 1 - (2 / 3) / math.log2(3)   # h(1/3) / log2 3 = 0.57938...
                for r in root:          # the frame map: every reading has entropy h(1/3)
                    self.assertAlmostEqual(root[r], frame, places=9)
            kinds = set()
            for sense, coefs, const, desc in model.rows:
                kinds.add(desc[0])
                if desc[0] == "read":
                    self.assertAlmostEqual(H(next(iter(k for k in coefs if k != model.t))),
                                           root[desc[2]], places=9)
                    continue
                val = sum(c * H(v) for v, c in coefs.items()) + const
                if sense == "ge":
                    self.assertGreaterEqual(val, -1e-9, desc)
                else:
                    self.assertAlmostEqual(val, 0.0, places=9, msg=str(desc))
            self.assertEqual(kinds, {"copy", "law", "norm", "read", "unif"})
            m = model.m
            full = (1 << m) - 1
            for _ in range(120):
                i, j = sorted(rng.sample(range(m), 2))
                K = rng.getrandbits(m) & full & ~(1 << i) & ~(1 << j)
                c = model.colof
                val = (H(c[K | (1 << i)]) + H(c[K | (1 << j)]) - H(c[K | (1 << i) | (1 << j)])
                       - H(c[K]))
                self.assertGreaterEqual(val, -1e-9)
            for _ in range(40):
                mk = rng.getrandbits(m) & full
                direct = klp.entropy_of_key(law, [model.forms[i] for i in klp.bits(mk)])
                self.assertAlmostEqual(H(model.colof[mk]), direct, places=9)


if __name__ == "__main__":
    unittest.main()
