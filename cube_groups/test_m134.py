# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of m134's list building (no tools, no network). Prints the result and exits 0, so
the job's logs show it; the check step's gates guard the real run."""
import sys
import unittest

import m134


def fake_census(n=48 * 3):
    return [f"case{i:03d}" for i in range(n)]


class T(unittest.TestCase):
    def test_order_hard_first(self):
        st = {"b": "NOT_STARTED", "a": "UNKNOWN", "c": "MISSING", "d": "DRAT_STOPPED",
              "e": "ERROR"}
        hard, fresh = m134.order(st)
        self.assertEqual(hard, ["a", "d", "e"])
        self.assertEqual(fresh, ["b", "c"])

    def test_chunks_partition(self):
        xs = [f"x{i}" for i in range(76)]
        chunks = [m134.chunk_of(xs, c) for c in range(m134.NCHUNK)]
        flat = [y for ch in chunks for y in ch]
        self.assertEqual(sorted(flat), sorted(xs))
        self.assertEqual(len(set(flat)), len(flat))
        sizes = [len(ch) for ch in chunks]
        self.assertLessEqual(max(sizes) - min(sizes), 1)

    def test_hard_cases_lead_their_chunks(self):
        st = {f"h{i}": "UNKNOWN" for i in range(6)}
        st.update({f"f{i:02d}": "NOT_STARTED" for i in range(70)})
        hard, fresh = m134.order(st)
        ordered = hard + fresh
        for c in range(6):
            self.assertIn(m134.chunk_of(ordered, c)[0], hard)
            self.assertEqual(sum(1 for x in m134.chunk_of(ordered, c) if x in hard), 1)

    def test_collect(self):
        cen = fake_census()
        files = {}
        for k in range(3):
            xs = cen[k::48]
            rows = [{"instance": xs[0], "cert": "VERIFIED"},
                    {"instance": xs[1], "cert": "UNKNOWN"}]   # xs[2] has no row (stopped)
            files[m134.RESULTS + f"m133s{k:02d}_cert.json"] = rows

        def get(url):
            if url not in files:
                raise IOError("404")
            return files[url]

        status, verified, missing = m134.collect(cen, get, last=3)
        self.assertEqual(verified, 3)
        self.assertEqual(missing, [3])
        self.assertEqual(status[cen[1 * 48 + 0]], "UNKNOWN")
        self.assertEqual(status[cen[2 * 48 + 0]], "MISSING")
        self.assertEqual(len(status), 3 * 2 + 3)

    def test_tags(self):
        self.assertEqual(m134.tag("mopup", chunk=3), "m134c03")
        self.assertEqual(m134.tag("part", shard=25, third=2), "m134k25p2")
        self.assertEqual(m134.fname("m134c03", "cert"), "m134c03_cert.json")

    def test_caps(self):
        self.assertEqual(m134.PART_CADICAL, 1500.0)
        self.assertEqual(m134.PART_DRAT, 4000)
        self.assertGreater(m134.MOP_CADICAL, m134.PART_CADICAL)
        self.assertGreater(m134.MOP_DRAT_STOPPED, m134.MOP_DRAT)


if __name__ == "__main__":
    r = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {r.testsRun} failures {len(r.failures)} errors {len(r.errors)}",
          flush=True)
    sys.exit(0)
