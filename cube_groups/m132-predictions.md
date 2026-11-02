# Job m132: predictions (pre-registered 2026-11-02, before any shard ran)

MV2 of Munim, Inc. (mv2@munimtech.com). Made with AI agents working in MV2's name; no human
mathematician has checked this. Text CC BY 4.0, code Apache-2.0. Companion note: notes/a128.md.

## What runs

A stratified sample of the d = 0 block of (B7)_8 at the **sweep** CNF. The 1,500 d = 0 cases
(m130.by_name) sorted by name, minus m130's six pilot cases (all certified: m130 and m131), leave
1,494; the sample is the 120 names at indices floor(k * 1494 / 120), k = 0 .. 119. Shard a takes
k = 0, 3, 6, ..., b takes k = 1, 4, ..., c takes k = 2, 5, ... (40 each). Each shard runs its cases
one at a time with m113.certify at "sweep": CaDiCaL 1,500 s with an ASCII DRAT proof, drat-trim
4,000 s; no new case starts after 25,000 s; 1 CPU, 3 GB, 540 minutes.

## Predictions (per shard unless stated)

1. **check:** 40 distinct d = 0 cases, none a pilot case, m131's three cases among the six pilot
   cases, tools built. (Expected: holds.)
2. **controls:** m113's controls pass. (Expected: holds.)
3. **no error:** every row is VERIFIED, UNKNOWN, SAT or NOT_STARTED, never ERROR. (Expected: holds.)
4. **every finished case is UNSAT and VERIFIED** (no UNKNOWN at 1,500 s, no SAT at sweep).
   (Expected: holds in at least two of three shards; overall about 55%. m131's three hardest
   pilot cases needed at most 498 s.)
5. **median CaDiCaL time of the UNSAT cases <= 600 s.** (Expected: holds; the six pilot cases took
   67 to 498 s.)
6. **at least 20 cases finished** in the shard. (Expected: holds; about 1,000 s of wall time per
   case gives about 25.)
7. **no solution** (a SAT row whose model passes every m106 check, anisotropy included).
   (Expected: holds. A solution would mean (B7)_8 is not empty; it would be checked by an
   independent script before any claim.)

## Decision rule

- **4 holds in all three shards:** d = 0 is decidable at sweep at a fixed cap. Plan the census of
  the remaining ~1,370 cases in shards of the same form (about 25 cases each), a few shards per
  day so the shared machine is not monopolised, and publish counts as they land.
- **Some UNKNOWN at 1,500 s:** list them; each goes alone to a long job (CaDiCaL 14,400 s) or to
  cubing (m121's pattern) before the census.
- **A SAT row that is not a solution:** stop and find which check fails; a spurious model at sweep
  would mean the sweep CNF is weaker than m106's checks.
- **A solution:** stop the d = 0 work and re-check the model independently (group order, Omega_1,
  the inequality itself), then write it up.
