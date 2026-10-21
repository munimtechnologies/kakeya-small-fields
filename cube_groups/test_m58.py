# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Fast tests of m58.py (job m58). The hand counts (d of each class, ranks on X_1, instance sizes)
are graded in --part check, so a wrong hand number is a graded failure, not a crashed job."""
import unittest

import m57
import m58 as m


class TestM58(unittest.TestCase):
    def test_lists(self):
        b6 = m.open_b6()
        self.assertEqual(len(b6), len(m.OPEN_M45) + len(m.OPEN_M47))
        self.assertFalse(set(m.OPEN_M45) & set(m.OPEN_M47))
        for name in b6:
            pi, ci = m57.pair_cls(name)
            self.assertEqual(name, f"r3b_t7_B6_o{pi:03d}_c{ci:03d}")
            self.assertIn(pi, m.B6_PAIR_R)
            self.assertNotIn(pi, (0, 1, 2))

    def test_plan(self):
        a, b = m.plan("a"), m.plan("b")
        self.assertEqual(len(a), 3 + len(m.GRAPH_B))
        self.assertEqual([(s["name"], arm) for s, arm, _, _, _ in a[:3]],
                         [("r3g_t7_B6_o002_a025", "cadical"), ("r3g_t7_B6_o002_a025", "xor"),
                          ("r3g_t7_B6_o002_a085", "cadical")])
        self.assertEqual(a[1][3], "a025_open")
        self.assertTrue(all(arm == "cadical" and cap == 95.0 and not named
                            for _, arm, cap, _, named in a[3:]))
        self.assertEqual(a[3][0]["name"], "r3g_t7_B6_o002_a089")
        self.assertEqual(a[-1][0]["name"], f"r3g_t7_B6_o002_a{88 + len(m.GRAPH_B):03d}")
        self.assertEqual(len(b), len(m.open_b6()))
        self.assertTrue(all(arm == "xor" and cap == 180.0 for _, arm, cap, _, _ in b))

    def test_specs(self):
        sp = m.graph_spec(*m.A025)
        self.assertEqual((sp["t"], sp["d"], sp["p"], sp["pair"]), (7, 9, 6, 2))
        self.assertEqual(sp["au"], m.GRAPH_AU)
        t, d, au, s0, phis, kd, pvecs = m57.params(sp)
        self.assertEqual((au, s0, kd), (m.GRAPH_AU, 1, 3))
        b = m.b6_spec("r3b_t7_B6_o012_c011", m.OPEN_M47["r3b_t7_B6_o012_c011"])
        self.assertEqual(b["r"], [64, 32, 17])
        self.assertEqual(b["source"], "m47")

    def test_a025_map(self):
        self.assertEqual(m57.column(m.A025[3], 4), 8)       # e_4 -> e_3
        self.assertEqual(m57.rank_on_x1(m.A025[3]), 0)


if __name__ == "__main__":
    unittest.main()
