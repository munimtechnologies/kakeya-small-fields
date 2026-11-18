"""Tests for kakeya_sparse.py and sparse_cert_check.py (standard library only).

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Apache-2.0.

What is checked:
- Farnamfar's slope encoding and his five-page page construction rebuild over F_3 to the
  expected coordinates, identically in the LP builder and in the independent checker;
- the independent F_3 replay accepts small certificates written in Farnamfar's format
  (sub / ci rows, equal-law generators, lambda), detects the copy-identity sign, and
  rejects corrupted versions;
- the sparse model contains the Katz-Tao proof: an exact combination of its rows gives
  exactly 6/11, and the independent checker accepts the exported certificate;
- the checker rejects corrupted certificates;
- every row the LP can generate (copy, law orbits, norm, read, sub/mono neighbourhoods,
  cross forms with the Kakeya restriction) holds on exact realisations for explicit
  Kakeya maps of F_3.
"""

import unittest
from fractions import Fraction

import kakeya_lp as klp
import kakeya_sparse as ks
import sparse_cert_check as scc

std = ks.std
INF = float("inf")

PAGE_HEAD = [
    {"U": [0], "V": [[0, [1, 0]]]},
    {"U": [0, 1], "V": [[0, [0, 1]], [1, [0, 1]]]},
    {"U": [2, 3], "V": [[2, [1, 1]], [3, [0, 1]]]},
]
# glue word "..CCC." read in the order (2, 0, 4, 3, 1, 5): s of vertices 4, 3, 1
PAGE_CHAIN = PAGE_HEAD + [{"U": [0, 1, 2, 3, 4, 5], "V": [[4, [1, 1]], [3, [1, 1]], [1, [1, 1]]]}]


def e(i, R=5):
    return tuple(1 if j == i else 0 for j in range(R))


def tiny_eqlaw_cert():
    return {"steps": [{"U": [0], "V": [[0, [1, 0]]]}], "extra": [],
            "rows": [{"type": "sub", "K": [], "i": [1, [1, 0]], "j": [1, [0, 1]], "mult": "1"}],
            "eqlaw": [{"step": 0, "gens": [[0, [0, 1]]]},
                      {"step": 0, "gens": [[0, [1, 0]], [0, [0, 1]]]}],
            "lambda": {"1,0": "1", "0,1": "1", "1,1": "0"}, "claimed_C": "2"}


def tiny_ci_cert(ci_mult="1"):
    return {"steps": [{"U": [0], "V": [[0, [1, 0]]]}], "extra": [],
            "rows": [{"type": "ci", "step": 0, "mult": ci_mult},
                     {"type": "sub", "K": [[0, [1, 0]]], "i": [0, [0, 1]], "j": [1, [0, 1]],
                      "mult": "1"},
                     {"type": "sub", "K": [], "i": [0, [1, 0]], "j": [0, [0, 1]], "mult": "1"}],
            "eqlaw": [], "lambda": {"1,0": "1", "0,1": "1", "1,1": "0"}, "claimed_C": "2"}


# Katz-Tao word atoms as vertex readings (see test_kakeya_lp.py for the coordinates).
KT_ATOM = {0: std(0, "x"), 1: std(0, "y"), 2: std(1, "y"), 3: std(2, "x"), 4: std(2, "y"),
           5: std(3, "y"), 6: std(4, "x"), 7: std(6, "x"), 8: std(6, "y"), 9: std(0, "s"),
           10: std(1, "s"), 11: std(4, "s")}
KT_SUBS = [(0, 6, []), (1, 6, [0]), (2, 6, [0, 1]), (0, 8, []), (1, 8, [0]), (2, 8, [0, 1]),
           (6, 8, [0, 1, 2]), (9, 10, []), (4, 5, []), (5, 11, [])]


def kt_sparse():
    """The Katz-Tao proof as rows of a SparseModel. Returns (model, multipliers)."""
    M = ks.SparseModel(klp.KT_WORD)
    mults = {}

    def put(idx, mu):
        assert idx is not None
        mults[idx] = mults.get(idx, Fraction(0)) + Fraction(mu)

    for i, j, K in KT_SUBS:
        put(M.add_sub([KT_ATOM[k] for k in K], KT_ATOM[i], KT_ATOM[j]), 1)
    for s, mu in ((0, 3), (1, 1), (2, 1), (3, 1)):
        put(M.add_copy(s), mu)
    laws = [(1, [std(0, "x"), std(0, "y"), std(1, "y")], -3),
            (2, [std(2, "x"), std(2, "y"), std(3, "y")], -2),
            (3, [std(4, "y"), std(5, "y"), std(4, "x")], -1)]
    for s, S, mu in laws:
        put(M.add_law(s, S), mu)
    for v in (0, 1):
        put(M.add_norm(v), 3)
    for (v, r), mu in (((4, "x"), -1), ((6, "y"), -1), ((0, "s"), -1), ((1, "s"), -1),
                       ((2, "y"), -1), ((3, "y"), -2), ((4, "s"), -1), ((0, "x"), -3)):
        put(M.add_read(v, r), mu)
    return M, mults


def _check_rows(test, M, pmaps):
    kinds = set()
    for pmap in pmaps:
        law = klp.realize(M.cfg, pmap)
        test.assertEqual(sum(law.values()), 1)
        cache = {}

        def H(var):
            if var == 0:
                return 0.0
            if var not in cache:
                cache[var] = klp.entropy_of_key(law, M.keys[var])
            return cache[var]

        root = {r: klp.entropy_of_key(law, [M.cfg.reading(0, r)]) for r in ("x", "y", "s")}
        for sense, coefs, const, desc in M.rows:
            kinds.add(desc[0])
            if desc[0] == "read":
                var = next(k for k in coefs if k != M.t)
                test.assertAlmostEqual(H(var), root[desc[2]], places=9)
                continue
            test.assertNotIn(M.t, coefs)
            val = sum(c * H(v) for v, c in coefs.items()) + const
            if sense == "ge":
                test.assertGreaterEqual(val, -1e-9, str(desc))
            else:
                test.assertAlmostEqual(val, 0.0, places=9, msg=str(desc))
    return kinds


class TestEncoding(unittest.TestCase):
    def test_slope_kind(self):
        for fn in (ks.slope_kind, scc._slope_kind):
            self.assertEqual(fn(1, 0), "x")
            self.assertEqual(fn(0, 1), "y")
            self.assertEqual(fn(1, 1), "s")
            self.assertEqual(fn(1, -1), "d")
            self.assertEqual(fn(-1, 1), "d")
            self.assertEqual(fn(2, 2), "s")
            self.assertEqual(fn(2, 0), "x")
            self.assertEqual(fn(0, 2), "y")
        with self.assertRaises(ValueError):
            ks.slope_kind(0, 3)

    def test_farn_form(self):
        self.assertEqual(ks.farn_form([3, [1, -1]]), ((3, 1, 2),))
        with self.assertRaises(ValueError):
            ks.farn_form(["amb", 3])
        with self.assertRaises(ValueError):
            ks.farn_form([0, [0, 3]])

    def test_thresholds(self):
        self.assertLess(ks.KT_BOUND, ks.FARN_SHANNON)
        self.assertLess(ks.FARN_SHANNON, ks.FARN_RECORD)
        self.assertLess(abs(float(1 / ks.FARN_RECORD) - 1.8263483657186), 1e-9)

    def test_page_coordinates(self):
        word = ks.farn_word({"steps": PAGE_HEAD})
        self.assertEqual(word["steps"][2], {"block": [2, 3], "glue": [[2, "s"], [3, "y"]]})
        cfg = klp.Config(word)
        self.assertEqual(cfg.r, 5)
        a, b, c, d, ee = e(0), e(1), e(2), e(3), e(4)
        bde = (0, 1, 0, 1, 2)  # b + d - e
        expected = [(a, b), (a, c), (d, b), (d, c), (ee, bde), (ee, c)]
        self.assertEqual(cfg.vertices(), expected)
        R, X, Y, _ = scc.rebuild(word)
        self.assertEqual(R, 5)
        self.assertEqual(list(zip(X, Y)), expected)

    def test_chain_page_matches_checker(self):
        word = ks.farn_word({"steps": PAGE_CHAIN})
        cfg = klp.Config(word)
        self.assertEqual(len(cfg.vx), 12)
        self.assertEqual(cfg.r, 7)
        R, X, Y, steps = scc.rebuild(word)
        self.assertEqual(R, 7)
        self.assertEqual(list(zip(X, Y)), cfg.vertices())
        self.assertEqual(steps[3]["new"], list(range(6, 12)))
        # glued readings are shared: s of the copies of vertices 4, 3, 1 equal the originals
        for v in (4, 3, 1):
            self.assertEqual(cfg.reading(v, "s"), cfg.reading(v + 6, "s"))
        self.assertNotEqual(cfg.reading(0, "x"), cfg.reading(6, "x"))


class TestFarnReplay(unittest.TestCase):
    def test_eqlaw_certificate(self):
        r = scc.farn_replay(tiny_eqlaw_cert())
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["bound"], "1/2")
        self.assertTrue(r["claim_matches"])
        self.assertEqual(r["vertices"], 2)

    def test_missing_eqlaw_rejected(self):
        cert = tiny_eqlaw_cert()
        del cert["eqlaw"][0]
        self.assertFalse(scc.farn_replay(cert)["ok"])

    def test_wrong_multiplier_rejected(self):
        cert = tiny_eqlaw_cert()
        cert["rows"][0]["mult"] = "2"
        self.assertFalse(scc.farn_replay(cert)["ok"])

    def test_negative_sub_rejected(self):
        cert = tiny_eqlaw_cert()
        cert["rows"][0]["mult"] = "-1"
        with self.assertRaises(AssertionError):
            scc.farn_replay(cert)

    def test_ci_sign(self):
        r = scc.farn_replay(tiny_ci_cert("1"))
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["ci_sign"], 1)
        r = scc.farn_replay(tiny_ci_cert("-1"))
        self.assertTrue(r["ok"], r)
        self.assertEqual(r["ci_sign"], -1)
        bad = tiny_ci_cert("1")
        del bad["rows"][2]
        self.assertFalse(scc.farn_replay(bad)["ok"])

    def test_wrong_claim_flagged(self):
        cert = tiny_ci_cert("1")
        cert["claimed_C"] = "3"
        r = scc.farn_replay(cert)
        self.assertTrue(r["ok"])
        self.assertFalse(r["claim_matches"])

    def test_model_imports_same_rows(self):
        cert = tiny_ci_cert("1")
        M = ks.SparseModel(ks.farn_word(cert))
        ic = M.add_copy(0)
        i1 = M.add_sub([std(0, "x")], std(0, "y"), std(1, "y"))
        i2 = M.add_sub([], std(0, "x"), std(0, "y"))
        nv = M.add_norm(0)
        rx = M.add_read(0, "x")
        ry = M.add_read(0, "y")
        n = len(M.rows)
        base = M.add_farn_rows(cert)
        self.assertEqual(len(M.rows), n)
        self.assertEqual(len(base), 2)
        mults = {ic: Fraction(1), i1: Fraction(1), i2: Fraction(1), nv: Fraction(1),
                 rx: Fraction(-1), ry: Fraction(-1)}
        ok, bound, info = klp.combine(M, mults)
        self.assertTrue(ok, info)
        self.assertEqual(bound, Fraction(1, 2))
        cert2 = ks.export(M, M, bound, mults, False)
        self.assertEqual(scc.check(cert2), Fraction(1, 2))


class TestKatzTaoInSparseModel(unittest.TestCase):
    def test_combination_is_six_elevenths(self):
        M, mults = kt_sparse()
        ok, bound, info = klp.combine(M, mults)
        self.assertTrue(ok, info)
        self.assertEqual(bound, Fraction(6, 11))
        cert = ks.export(M, M, bound, mults, False)
        self.assertEqual(scc.check(cert), Fraction(6, 11))

    def test_corruptions_rejected(self):
        M, mults = kt_sparse()
        ok, bound, _ = klp.combine(M, mults)
        good = ks.export(M, M, bound, mults, False)

        def bad(edit):
            cert = ks.export(M, M, bound, mults, False)
            edit(cert)
            with self.assertRaises(AssertionError):
                scc.check(cert)

        self.assertEqual(scc.check(good), Fraction(6, 11))

        def mult_twice(c):
            c["rows"][0]["m"] = "2"

        def negative_sub(c):
            c["rows"][0]["m"] = "-1"

        def claim(c):
            c["claimed_bound"] = "7/11"

        def unif_without_flag(c):
            c["rows"].append({"d": {"k": "unif", "f": [[0, 1, 0]]}, "m": "1"})

        def law_outside_block(c):
            c["rows"].append({"d": {"k": "law", "step": 1, "S": [[[4, 1, 0]]]}, "m": "1"})

        for edit in (mult_twice, negative_sub, claim, unif_without_flag, law_outside_block):
            bad(edit)
        self.assertEqual(good["rows"][0]["d"]["k"], "sub")


class TestRowsHoldOnRealMaps(unittest.TestCase):
    """Every generated row must hold for genuine Kakeya maps of F_3 (k = 1)."""

    def test_kt_word_tiers(self):
        M = ks.SparseModel(klp.KT_WORD)
        M.add_copy_rows()
        M.add_norm_read()
        base = []
        for i, j, K in KT_SUBS:
            Ks = frozenset(KT_ATOM[k] for k in K)
            M.add_sub(Ks, KT_ATOM[i], KT_ATOM[j])
            base.append((Ks, KT_ATOM[i], KT_ATOM[j]))
        self.assertTrue(ks.tier_A(M, base, INF, 10 ** 9))
        self.assertTrue(ks.tier_C(M, base[:3], INF, 10 ** 9))
        M.add_law_orbits(rounds=1)
        kinds = _check_rows(self, M, ([0, 1, 1], [0, 0, 1], [2, 0, 1]))
        self.assertEqual(kinds, {"copy", "law", "norm", "read", "sub", "mono", "unif"})

    def test_chain_page_rows(self):
        M = ks.SparseModel(ks.farn_word({"steps": PAGE_CHAIN}))
        M.add_copy_rows()
        M.add_norm_read()
        base = [(frozenset(), std(0, "x"), std(7, "y")),
                (frozenset([std(4, "s")]), std(2, "x"), std(10, "y"))]
        for K, i, j in base:
            M.add_sub(K, i, j)
        self.assertTrue(ks.tier_A(M, base, INF, 10 ** 9))
        self.assertTrue(ks.tier_C(M, base[:1], INF, 10 ** 9))
        M.add_law_orbits(rounds=2)
        kinds = _check_rows(self, M, ([0, 1, 1], [1, 0, 0]))
        self.assertIn("law", kinds)
        self.assertIn("unif", kinds)


class TestDecide(unittest.TestCase):
    def test_verdicts(self):
        def rec(b):
            return [{"file": "f", "tiers": {"t0": {"checked_bound": b}}}]

        self.assertEqual(ks.decide([{"file": "f"}])["verdict"], "NO_CERTIFICATE")
        self.assertEqual(ks.decide(rec("83/152"))["verdict"], "NULL")
        self.assertEqual(ks.decide(rec("547/1000"))["verdict"], "SHANNON_GAIN")
        self.assertEqual(ks.decide(rec("548/1000"))["verdict"], "RECORD")


if __name__ == "__main__":
    unittest.main()
