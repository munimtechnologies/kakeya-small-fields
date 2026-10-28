# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests for m124.py (job m124, cube_groups/m124-predictions.md). Needs m121.py, m122.py, m113.py,
the modules they import and the grade files of m110a-j, m111b-c, m112a-l, m114a-f, m116a-b and m119
next to it. The solver is replaced by a table keyed by the node's sign string (1 = true), so the tree
logic is tested without CaDiCaL. Expectations worked out by hand:

- A_(h_1) with variables [[1, 2], [3, 4]] and clauses [1], [2, 3], [-2, 3], [3, -4], [2, 5]: 1 is
  fixed; 2 and 3 occur three times, 4 and 5 once. The order is [2, 3, 4] from A_(h_1), then [5];
  with k = 2 it is [2, 3].
- units([5, 7, 9], (True, False)) is [5, -7].
- Order [5, 7, 9], table: root UNKNOWN, "1" UNSAT, "0" UNKNOWN, "01" UNSAT, "00" UNKNOWN, "001" and
  "000" UNSAT. The tree has 7 nodes; the root, "0" and "00" are split; the 4 leaves weigh 1/2 + 1/4
  + 1/8 + 1/8 = 1, all UNSAT, so the verdict is UNSAT. Only the depth-3 nodes get the leaf cap.
- The same with "000" UNKNOWN: it is at the maximum depth, so it is not split; weight 1, OPEN.
- With "1" SAT (a model that satisfies the CNF) the verdict is SAT.
- force = 2 with every depth-2 node UNSAT: 3 FORCED nodes (1 + 2), 4 UNSAT leaves, UNSAT; nothing
  above depth 2 is solved.
- tree_verdict: no leaves gives OPEN; an incomplete set of UNSAT leaves ("1" alone) gives OPEN.
- The real grade files load and every open case is a d = 1 case; the count (30) is graded in the
  check part.
"""
import os
import tempfile
import time
import types
import unittest

import m104
import m113
import m121
import m124

A = [None] * m121.H1 + [[[1, 2], [3, 4]]]
NAMES = (A,)
CLAUSES = [[1], [2, 3], [-2, 3], [3, -4], [2, 5]]
ORDER = [5, 7, 9]
CNF = types.SimpleNamespace(clauses=[[1, 2]], nv=9)


class FakeSolver:
    """Stands in for m104.write_dimacs / run_cadical / model_of / satisfied."""

    def __init__(self, table):
        self.table, self.caps = table, {}

    def write_dimacs(self, clauses, nv, path):
        open(path, "w").close()

    def run_cadical(self, tools, path, proof, cap):
        key = os.path.basename(path)[1:-4]
        self.caps[key] = cap
        return {"status": self.table[key], "seconds": 1.0}, "v 1 2 0"

    def __enter__(self):
        self.saved = (m104.write_dimacs, m104.run_cadical, m104.model_of, m104.satisfied)
        m104.write_dimacs, m104.run_cadical = self.write_dimacs, self.run_cadical
        m104.model_of = lambda text: [1, 2]
        m104.satisfied = lambda clauses, model: True
        return self

    def __exit__(self, *exc):
        m104.write_dimacs, m104.run_cadical, m104.model_of, m104.satisfied = self.saved


def run_tree(table, force=0):
    with FakeSolver(table) as fake, tempfile.TemporaryDirectory() as tmp:
        rows = m124.conquer("tools", CNF, ORDER, 90.0, 1200.0, 2, time.time() + 600, tmp, force)
    return rows, fake.caps


BASE = {"": "UNKNOWN", "1": "UNSAT", "0": "UNKNOWN", "01": "UNSAT", "00": "UNKNOWN",
        "001": "UNSAT", "000": "UNSAT"}


class TestM124(unittest.TestCase):
    def test_order_and_units(self):
        self.assertEqual(m124.order_vars(CLAUSES, NAMES, 10), [2, 3, 4, 5])
        self.assertEqual(m124.order_vars(CLAUSES, NAMES, 2), [2, 3])
        self.assertEqual(m124.units([5, 7, 9], (True, False)), [5, -7])

    def test_unsat_tree(self):
        rows, caps = run_tree(BASE)
        self.assertEqual(len(rows), 7)
        self.assertEqual(sorted("".join("1" if s else "0" for s in r["signs"])
                                for r in rows if r.get("split")), ["", "0", "00"])
        self.assertEqual(m124.leaf_weight(rows), 1)
        self.assertEqual(m124.tree_verdict(rows), "UNSAT")
        self.assertEqual(caps["000"], 1200.0)
        self.assertEqual(caps["001"], 1200.0)
        self.assertEqual(caps["00"], 90.0)
        self.assertEqual(caps[""], 90.0)

    def test_open_at_max_depth(self):
        rows, _ = run_tree(dict(BASE, **{"000": "UNKNOWN"}))
        self.assertEqual(len(rows), 7)
        self.assertEqual(m124.leaf_weight(rows), 1)
        self.assertEqual(m124.tree_verdict(rows), "OPEN")

    def test_sat(self):
        rows, _ = run_tree(dict(BASE, **{"1": "SAT"}))
        self.assertEqual(m124.tree_verdict(rows), "SAT")
        sat = [r for r in rows if r["status"] == "SAT"]
        self.assertTrue(sat and all(r["satisfies_cnf"] for r in sat))

    def test_force(self):
        table = {"11": "UNSAT", "10": "UNSAT", "01": "UNSAT", "00": "UNSAT"}
        rows, caps = run_tree(table, force=2)
        self.assertEqual(sum(r["status"] == "FORCED" for r in rows), 3)
        self.assertEqual(sorted(caps), ["00", "01", "10", "11"])
        self.assertEqual(m124.leaf_weight(rows), 1)
        self.assertEqual(m124.tree_verdict(rows), "UNSAT")

    def test_verdict_edges(self):
        self.assertEqual(m124.tree_verdict([]), "OPEN")
        self.assertEqual(m124.tree_verdict([{"signs": [True], "status": "UNSAT"}]), "OPEN")

    def test_real_files_load(self):
        # the count itself is a graded check of the check part, not a test failure
        names = m124.open_cases()
        self.assertIsNotNone(names)
        cases = m113.d1_cases()
        self.assertTrue(all(x in cases for x in names))


if __name__ == "__main__":
    unittest.main()
