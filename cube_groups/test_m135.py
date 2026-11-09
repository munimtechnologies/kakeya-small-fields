# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Unit tests of m135's list building (no tools, no network). Prints the result and exits 0, so
the job's logs show it; the check step's gates guard the real run."""
import sys
import unittest

import m134
import m135


class T(unittest.TestCase):
    def test_tags(self):
        self.assertEqual(m135.tag("a", 2), "m135a02")
        self.assertEqual(m135.tag("b", 0), "m135b00")
        self.assertEqual(m135.fname("m135a02", "cert"), "m135a02_cert.json")

    def test_collect(self):
        srcs = [("s1", "u1", ["a", "b", "c"]), ("s2", "u2", ["d", "e"]), ("s3", "u3", ["f"])]
        files = {"u1": [{"instance": "a", "cert": "VERIFIED"},
                        {"instance": "b", "cert": "NOT_STARTED"}],      # c: no row (stopped)
                 "u2": [{"instance": "d", "cert": "VERIFIED"},
                        {"instance": "e", "cert": "UNKNOWN"}]}         # s3 not published

        def get(url):
            if url not in files:
                raise IOError("404")
            return files[url]

        status, verified, missing = m135.collect(srcs, get)
        self.assertEqual(verified, 2)
        self.assertEqual(missing, ["s3"])
        self.assertEqual(status, {"b": "NOT_STARTED", "c": "MISSING", "e": "UNKNOWN",
                                  "f": "MISSING"})
        hard, fresh = m134.order(status)
        self.assertEqual(hard, ["e"])
        self.assertEqual(fresh, ["b", "c", "f"])

    def test_scope_a(self):
        sc = m135.SCOPES["a"]
        self.assertEqual(sc["m133_shards"], [22, 23, 24])
        self.assertEqual(sc["parts"], [(25, 0)])
        # 29 + 29 + 29 + 10 cases in the four cert files
        self.assertEqual(sc["expect_verified"] + sc["expect_mopup"], 29 * 3 + 10)
        xs = [f"x{i:02d}" for i in range(sc["expect_mopup"])]
        chunks = [m134.chunk_of(xs, c, sc["nchunk"]) for c in range(sc["nchunk"])]
        self.assertEqual(sorted(y for ch in chunks for y in ch), xs)
        self.assertEqual([len(ch) for ch in chunks], [8, 7, 7])

    def test_scope_b(self):
        sc = m135.SCOPES["b"]
        self.assertEqual(sc["m133_shards"], [])
        self.assertEqual(sc["parts"], [(25, 1), (25, 2)])
        # k25p1 has 10 cases, k25p2 has 9 (shard 25 has 29 cases, thirds [P::3])
        self.assertEqual(sc["expect_verified"] + sc["expect_mopup"], 10 + 9)
        # the open rows of the published cert files (a142, a143)
        status = {"r3b_t8_B7_o012_c011_t2_m069": "UNKNOWN",          # k25p1
                  "r3b_t8_B7_o012_c007_t3_m007_179": "DRAT_STOPPED",  # k25p1
                  "r3b_t8_B7_o012_c003_t2_m227": "UNKNOWN",          # k25p2
                  "r3b_t8_B7_o012_c006_t2_m248": "NOT_STARTED",      # k25p2
                  "r3b_t8_B7_o012_c008_t3_m002_132": "NOT_STARTED"}  # k25p2
        hard, fresh = m134.order(status)
        self.assertEqual(len(hard), sc["expect_hard"])
        self.assertEqual(len(hard) + len(fresh), sc["expect_mopup"])
        ordered = hard + fresh
        chunks = [m134.chunk_of(ordered, c, sc["nchunk"]) for c in range(sc["nchunk"])]
        self.assertEqual(chunks[0], ["r3b_t8_B7_o012_c003_t2_m227",
                                     "r3b_t8_B7_o012_c006_t2_m248"])
        self.assertEqual(chunks[1], ["r3b_t8_B7_o012_c007_t3_m007_179",
                                     "r3b_t8_B7_o012_c008_t3_m002_132"])
        self.assertEqual(chunks[2], ["r3b_t8_B7_o012_c011_t2_m069"])
        # every chunk holds exactly one hard case
        for ch in chunks:
            self.assertEqual(sum(1 for x in ch if x in hard), 1)

    def test_caps_match_m134_mopup(self):
        self.assertEqual(m135.MOP_CADICAL, 4000.0)
        self.assertEqual(m135.MOP_DRAT, 6000)
        self.assertEqual(m135.MOP_DRAT_STOPPED, 10000)
        self.assertEqual(m135.NO_START_AFTER, 12000)


if __name__ == "__main__":
    r = unittest.main(exit=False, verbosity=2).result
    print(f"SUMMARY tests run {r.testsRun} failures {len(r.failures)} errors {len(r.errors)}",
          flush=True)
    sys.exit(0)
