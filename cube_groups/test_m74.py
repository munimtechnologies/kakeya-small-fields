# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m74.py. The machine counts are not tested here; the job grades them."""
import copy
import unittest

import m55
import m57
import m74


def fake_result(name):
    mask, x1, rb = m74.CLASSES[name]
    st = m55.structure(m55.cols_of(mask), x1, rb)
    order = m74.HAND_ORDER[name]
    return {"name": name, "au": mask, "x1": list(x1), "r": list(rb), "structure": st,
            "order": order, "order_hand": order, "group_checked": True, "valid": 405566,
            "valid_hand": m55.HAND_VALID[x1], "fast_matches_slow": True, "linear_ok": True,
            "action_closed": True, "orbits": m74.HAND_LOWER[name] + 5,
            "lower_bound": -(-405566 // (2 * order)),
            "orbits_by_rank_x1": {"0": 2, "1": m74.HAND_LOWER[name], "2": 3}, "sizes_ok": True}


class TestM74(unittest.TestCase):
    def test_installed(self):
        m74.install()
        self.assertIs(m55.CLASSES, m74.CLASSES)
        self.assertIs(m55.HAND_ORDER, m74.HAND_ORDER)
        self.assertEqual(set(m74.HAND_ORDER), set(m74.CLASSES))
        self.assertEqual(set(m74.HAND_LOWER), set(m74.CLASSES))

    def test_classes(self):
        for name, (mask, x1, rb) in m74.CLASSES.items():
            pair, _ = m57.pair_cls(name)
            self.assertEqual(m57.LEFTOVERS[name], mask)
            self.assertEqual(tuple(m57.PAIR_R[pair]), rb)
            self.assertEqual(m57.x1_of(pair), x1)
            self.assertEqual(x1, m55.ALPHA)
            st = m55.structure(m55.cols_of(mask), x1, rb)
            self.assertEqual(st["rank_au"], 3)
            self.assertTrue(st["ker_is_x1"] and st["im_is_r"] and st["x1_in_h0"])
            self.assertFalse(st["d3"])
            self.assertEqual(m74.meet_dim(x1, rb), 2)
            self.assertEqual(m57.meet_d(m57.b5_spec(name, mask)), 2)
            self.assertEqual(m55.HAND_VALID[x1], 405566)
            self.assertEqual(-(-405566 // (2 * m74.HAND_ORDER[name])), m74.HAND_LOWER[name])

    def test_maps(self):
        for name, (mask, x1, rb) in m74.CLASSES.items():
            mp = m55.Maps(x1, rb)
            au = m55.cols_of(mask)
            idx = mp.index(au)
            self.assertEqual(mp.cols(idx), au)
            self.assertEqual(mp.rank_x1(idx), 0)
            self.assertTrue(mp.base_slow(idx))
            self.assertEqual(list(mp.base_block(idx & ((1 << 15) - 1)))[idx >> 15], 1)

    def test_grade(self):
        results = {n: fake_result(n) for n in m74.CLASSES}
        g = m74.grade(results)
        self.assertTrue(g["all_held"])
        self.assertEqual(g["total"], 5 * len(m74.CLASSES))
        self.assertEqual(g["split_rank12"]["o004_c001"], 103)
        self.assertEqual(g["split_rank12_total"], sum(m74.HAND_LOWER.values()) + 9)
        for key, bad in (("order", 1), ("valid", 405565), ("action_closed", False),
                         ("orbits", 1), ("sizes_ok", False)):
            r = copy.deepcopy(results)
            r["r3b_t7_B5_o005_c005"][key] = bad
            self.assertFalse(m74.grade(r)["all_held"], key)
        r = copy.deepcopy(results)
        r["r3b_t7_B5_o006_c000"]["r"] = [4, 2, 1]
        self.assertFalse(m74.grade(r)["all_held"])


if __name__ == "__main__":
    unittest.main()
