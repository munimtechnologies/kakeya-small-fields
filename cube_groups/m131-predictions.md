# Job m131: predictions (pre-registered 2026-11-02, before any shard ran)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Text CC BY 4.0, code Apache-2.0. Companion note: notes/a127.md.

## What runs

Three shards, one case each, at the **sweep** CNF (m113.certify, mode "sweep"): CaDiCaL 4,800 s
with an ASCII DRAT proof, drat-trim 25,000 s.

| shard | case | m130 at "n" (600 s) |
|---|---|---|
| a | r3b_t8_B7_o012_c003_t2_m204 | SAT in 3.68 s; model passes every m106 check except `anisotropic` |
| b | r3b_t8_B7_o012_c002_t2_m085 | UNKNOWN (0.93 GB proof at the cap) |
| c | r3b_t8_B7_o012_c005_t2_m170 | UNKNOWN (1.17 GB proof at the cap) |

This is the step m130-predictions.md's decision rule names: a SAT case at "n" goes to the sweep
CNF, and with fewer than 4 of 6 pilot cases UNSAT at "n", the rest go to the sweep CNF one case per
job before any sharding.

## Predictions (per shard unless stated)

1. **check:** the case is one of m130's 1,500 d = 0 cases, its class has dmeet = 0, both
   programs are built. (Expected: holds for a, b, c.)
2. **controls:** m113's four controls pass. (Expected: holds.)
3. **no error:** m113.certify builds the sweep CNF for a d = 0 class without an exception. It
   has only been called at "sweep" for d = 1 and d = 2 classes before, so this is a real test.
   (Expected: holds; about 80% sure.)
4. **a is UNSAT at sweep within 4,800 s.** The "n" model fails only anisotropy on V, and the
   sweep CNF adds anisotropy on V. (Expected: holds; about 85% sure.)
5. **b and c are UNSAT at sweep within 4,800 s.** d = 1 cases that were open at "n" needed 504 to
   7,074 s alone at sweep. (Expected: at least one of b, c holds; both about 60%.)
6. **Every UNSAT is drat-trim VERIFIED within 25,000 s.** (Expected: holds.)
7. **No shard returns a solution** (a SAT row whose model passes every m106 check, anisotropy
   included). (Expected: holds. A solution would mean (B7)_8 is not empty, so the route to
   A(8) <= 10 through (B7)_8 would fail; it would be checked by hand before any claim.)

## Decision rule

- **All three VERIFIED:** d = 0 is decidable one case per job at sweep. Then plan the census:
  m132 shards all 1,500 d = 0 cases at "n" with 600 s (m110's pattern, about 10 shards, one case
  at a time), certify every UNSAT, and send the rest to sweep one or two per job.
- **Some UNKNOWN at 4,800 s:** run that case again alone with CaDiCaL at 14,400 s, or try cubing
  (m121's pattern) on it, before sharding d = 0.
- **ERROR at sweep for d = 0 (prediction 3 fails):** read the traceback, fix the sweep CNF builder
  for dmeet = 0 in a new module, re-run the same case (m131 -v2).
- **A solution (prediction 7 fails):** stop the d = 0 work, re-check the model with an
  independent script (group order, Omega_1, the inequality itself), and write it up as a negative
  result for the A(8) <= 10 route.
