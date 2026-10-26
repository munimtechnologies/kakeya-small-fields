# Job m110: predictions, written 2026-10-26 in the run that started at 00:29Z, before the job ran

MV2 of Munim, Inc. Made with AI agents working in MV2's name. Text CC BY 4.0, code Apache-2.0.

Jobs m108a-d came back (notes/a102.md): drat-trim verified the DRAT proofs of all 1,115 d = 2
cases with k(T(N)) <= 4, so Proposition 39 holds (computer-assisted): in the rank-0 case of (B7)_8,
no case with k <= 4 in a class with d >= 2 is possible. Jobs m109h, i and j came back too: the
deletion-minimal systems keep 8 to 10 basis indices of V and 798 to 1,980 equations of (*), so a
hand proof of Lemma 110 along that route is not promising. Job m109g (three core cases) had not
come back when this was written.

Job m110 (cube_groups/m110.py; jobs m110a to m110j) imports m100.py to m106.py unchanged. It takes
the 3,876 cases with k <= 4 of the 34 d = 1 classes (job m104a's count), split into ten shards
(388 cases in a-f, 387 in g-j). Each job:

    check     the classes and counts against m104a, this shard's share, N's 15 vectors
    controls  o000_c000 t2_m511, o011_c000 t3_m001_016 and o007_c008 t2_m012 at "n" (all three
              SAT in earlier jobs); each must be SAT with a verified model
    run       pass 1: every case of the shard at "n" (m102's relax CNF plus anisotropy on the 15
              non-zero vectors of N; 60 s); pass 2: m102's sweep CNF (full anisotropy; 120 s) on
              each case that was not UNSAT at "n"; 200 minutes in all
    grade     the checks below

## Graded (each must hold)

- Unit tests pass (6 in test_m110) in each job.
- Check: 34 d = 1 classes, 3,876 distinct cases, by class equal to m104a's count, all d = 1 and
  k <= 4, no t1, job m106b's SAT case and three UNKNOWN cases among them, every type one of the six
  types with k <= 4, this shard's size, N's 15 vectors, the three controls by name.
- Controls: all three SAT, each model verified outside the encoder.
- No ERROR; every SAT model verified; every case of the shard ran at "n" or was skipped for time;
  the sweep CNF ran (or was skipped for time) on exactly the cases not UNSAT at "n".

## Exploratory

- UNSAT at "n" for at least 85% of the 3,876 cases: about 60%.
- UNSAT after both passes for at least 95%: about 45%. For all 3,876: about 10%.
- o007_c008 t2_m012 (SAT at "n" in m106b) UNSAT at the sweep: about 50%.
- Every one of the six types at least 80% UNSAT after both passes: about 50%.
- The classes with Kbar of order 1 (179 cases each) have a lower UNSAT share than the others:
  about 40%.
- Mean time of an UNSAT answer at "n" under 15 s: about 70%.
- Nothing skipped in any shard: about 55%.
- A verified model anisotropic on all of V (at either pass): about 2%.
- Peak memory at most 1 GB in every shard: about 90%.

## Decision rules

- **A graded check fails:** nothing in that job counts until it is explained.
- **A verified model anisotropic on all of V:** a system with t = 8 and dim V = 11 (A(8) = 11).
  Re-check it by brute force in a separate job before saying anything.
- **All 3,876 UNSAT:** DRAT certificates for each (the CNF that was UNSAT for it, as m108), job
  m111; if all verify, Proposition 40: in the rank-0 case of (B7)_8, no case with k <= 4 in a class
  with d >= 1 is possible.
- **Some open:** certify the UNSAT ones (m111) and re-run the open ones with the sweep CNF at a
  longer cap (600 s), by type.
- **Many cases SAT at "n" but UNSAT at the sweep:** at d = 1, as at d = 0, the refutations need
  anisotropy outside N; record which types.
