# Copyright 2026 MV2 of Munim, Inc. Licensed under the Apache License, Version 2.0 (Apache-2.0).
"""Job m62: the next passes over (B5) at t = 7 and dim V = 9, under the rules that job m60 wrote
down before it ran (cube_groups/m60-predictions.md; notes/a51.md).

m60a and m60b emptied r3b_t7_B5_o001_c000 and o002_c000 and split two more d = 3 classes by the
second matrix A_(h_1) (Proposition 32) at CaDiCaL budgets of 20 s: r3b_t7_B5_o032_c000 851 of 856
UNSAT, o000_c000 662 of 671. m60's rule for a split with 1 to 30 open: CaDiCaL for 5 minutes, then,
if still open, CryptoMiniSat with native XOR for 5 minutes. The 14 open instances are split over
two groups of 7 (m62a, m62b), each at most 70 minutes. What is left of each group's time goes to
the next class in the playbook's order, split the same way with CaDiCaL at most 20 s per instance:

Group a (job m62a): the 5 open of o032_c000 and a031, a098 of o000_c000, then the split of
  r3b_t7_B5_o000_c001 (1798 instances).
Group b (job m62b): the other 7 open of o000_c000, then the split of r3b_t7_B5_o000_c002 (1827).

This is m60.py, imported unchanged, with its lists replaced by the ones below (install()): every
function that builds, checks, solves and grades is m60's, so the check recomputes m55's classes
and representatives for the four classes used and compares each of the 14 instances with the
A_(h_1) that m60 ran. M60 plays the part of m60.M59B: the totals that the re-opened instances
add to.

Usage: python m62.py --part check|solve|grade [--group a|b] [--group-minutes 150] [--out-dir DIR]
"""
import m60

O32 = "r3b_t7_B5_o032_c000"
O0 = "r3b_t7_B5_o000_c000"
C1 = "r3b_t7_B5_o000_c001"
C2 = "r3b_t7_B5_o000_c002"
# The instances m60 left UNKNOWN at 20 s: (class, m55 order k, m55 index, rank on X_1, A_(h_1)),
# copied from m60a's and m60b's out/r3s_t7_B5_o0??_c000_aKKK__cadical.json.
REOPEN = {
    "a": ((O32, 14, 64, 0, 35184372088832), (O32, 23, 128, 0, 131072),
          (O32, 53, 576, 0, 105553116266496), (O32, 83, 1024, 0, 262144),
          (O32, 574, 2097152, 1, 281474976710656),
          (O0, 31, 512, 0, 262144), (O0, 98, 2048, 0, 16)),
    "b": ((O0, 123, 3072, 0, 2064), (O0, 155, 8704, 0, 266240), (O0, 162, 65536, 0, 8192),
          (O0, 273, 73728, 0, 12288), (O0, 277, 74240, 0, 274432),
          (O0, 308, 262144, 0, 134217728), (O0, 363, 270848, 0, 134483968)),
}
# m60's totals for the two split classes: (instances, UNSAT).
M60 = {O32: (856, 851), O0: (671, 662)}
TAIL = {"a": C1, "b": C2}
# m55's counts (m55-b5split-v1 out/m55_*.json) for every class used here.
GATE = {O32: {"orbits": 856, "by_rank": {"0": 18, "1": 387, "2": 451}},
        O0: {"orbits": 671, "by_rank": {"0": 133, "1": 416, "2": 122}},
        C1: {"orbits": 1798, "by_rank": {"0": 343, "1": 1136, "2": 319}},
        C2: {"orbits": 1827, "by_rank": {"0": 343, "1": 1164, "2": 320}}}
REPS_FILE = "m62_reps.json"


def install():
    """Point m60's lists at m62's."""
    m60.REOPEN, m60.M59B, m60.TAIL, m60.GATE = REOPEN, M60, TAIL, GATE
    m60.REPS_FILE = REPS_FILE


install()


def main():
    install()
    m60.main()


if __name__ == "__main__":
    main()
