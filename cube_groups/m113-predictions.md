# Job m113: predictions (written 2026-10-26 ~18:10 UTC, before any m113 job ran)

Job m113 (m113.py, six shards a-f, two cases at a time per shard) produces DRAT certificates
for the 3,075 d = 1 cases with k(T(N)) <= 4 of the rank-0 case of (B7)_8 that jobs m110a-h and
m110j refuted without certificates (notes/a103.md, notes/a104.md): 3,062 with m106's "n" CNF
(m102's relax CNF with sigma != 0 on the 15 non-zero vectors of N) and 13 with m102's sweep CNF at
120 s. Each case is certified as exactly the CNF that was UNSAT for it (a unit test checks that
m108.build_cert's "n" CNF is m106's, clause for clause). Tools and controls as in jobs m104 and m108
(cert1_tools.py: CaDiCaL with an ASCII DRAT proof, drat-trim), plus a positive control new to this
job: the "n" CNF of m110's d = 1 control o007_c008 t2_m012 must be SAT under the CaDiCaL binary, with
a model that satisfies the CNF and passes m106's checks of the system.

Jobs m112a-l (the 399 open cases, sweep CNF at 1,500 s) and the re-filed m110i (387 cases) are
still running; their UNSAT answers will be certified by a later job.

## Graded checks (each must hold; any that fails is reported, not explained away)

- check_*: grade files loaded; 3,075 decided = 3,062 "n" + 13 "sweep"; all are d = 1 cases; 414
  open; this shard's share (513 for a-c, 512 for d-f); the control SAT at "n" in m110; tools built.
- controls_*: php(6,5) UNSAT with a VERIFIED proof; an empty proof rejected; php(5,5) SAT with a
  model; the "n" control SAT with a verified model.
- all_accounted, no_sat, all_verified (every case that ran is VERIFIED), clauses_uniform.

## Predictions (probabilities are MV2's agents' own estimates)

1. Every check and control passes in all six shards: 90%.
2. Every case that runs is VERIFIED (no NOT_VERIFIED, no DRAT_STOPPED, no UNKNOWN): 90%. Earlier
   certificate jobs went 1,172 of 1,172.
3. No case is SAT under the CaDiCaL binary: 99% (a SAT would mean pysat's CaDiCaL 1.9.5 and the
   binary disagree on the same CNF, or a build that is not deterministic: a bug to find, not a
   counterexample, unless the model passes m106's checks AND is anisotropic on all of V).
4. No case is skipped for time in any shard: 75%. (Guess: 20-40 s per "n" case in all, two at a
   time, so about 1.5-3 hours of a 200-minute budget per shard.)
5. Mean CaDiCaL time per "n" case between 4 and 20 s: 70% (pysat's mean was about 8-9 s).
6. Mean drat-trim time per "n" case at most the mean CaDiCaL time: 60% (m108's d = 2 sweep cases:
   drat sum / CaDiCaL sum = 0.71 to 0.80).
7. Largest proof below 400 MB: 80% (m108's largest: 365 MB).
8. The 13 sweep cases take longer per case than the median "n" case: 85%.
9. Peak memory of a shard below 2.5 GB: 80%.

## Decision rules

- All VERIFIED -> the 3,075 cases count as certified. When m112a-l and m110i are back, certify their
  UNSAT answers the same way (the sweep CNF at up to 1,500 s needs longer caps: pilot three first)
  and, if every one of the 3,876 cases is certified, write Proposition 40 (no case of the 34 d = 1
  classes with k <= 4 extends to an anisotropic system).
- Any NOT_VERIFIED or DRAT_STOPPED -> re-run those cases alone with caps doubled; if one fails
  again, check its CNF hash against a fresh build and stop before claiming anything.
- Any skipped -> a follow-up job on exactly the skipped cases, same code and caps.
- Any SAT -> stop; read the model back (satisfies_cnf, the system, anisotropy on all of V).
- A failed control -> nothing from that shard counts.

The result stays computer-assisted. A certificate certifies the CNF, not the hand lemmas that
reduced the problem to it, and no human mathematician has checked either.
