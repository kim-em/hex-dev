# hex-primality: bench families (native and kernel)

## Accomplished

- `bench/HexPrimality/Bench.lean`: four families. The decision,
  certificate-search, and checker rows share a fixed ladder of primes
  at 31/61/123/256/511 bits with `n - 1 = k · 2^m` and `k` factoring
  over the committed table, so the search is deterministic trial
  division and no rho variance enters; certificates are committed
  literals with an elaboration `#guard` that each replays and is about
  its own input. `runSegment` prices `primesIn`. Bench verify runs in
  2 s, far inside the wallclock cap.
- `bench/HexBench/PrimalityKernel.lean` +
  `lean_lib HexPrimalityKernelProbe`: build-only kernel-replay probes,
  one `decide +kernel` `checkPrime` replay per rung on the same
  certificates — the 511-bit replay checks in about a second, which is
  the kernel side of the powModNat-versus-Montgomery question. Swept
  by fresh-module builds, not in-process timing (`proof_probes` is
  reserved for mathlib layers).
- `libraries.yml` phase4 block: the PrimeCert comparator recorded as
  informational with the toolchain-pin rationale (PARI is the oracle,
  not a performance comparator), and the two input families named.
  Lakefile/CI registrations; probe lib added to the build-only lists
  in `libgraph.py`/`check_dag.py`.

## Current frontier

Everything in the SPEC is now landed except the sieve (milestone 1's
second half: Sieve.lean, SieveElab, and the verification swap), which
the SPEC itself allows to trail.

## Next step

PR4: the kernel-reducible bitset sieve and `sieve_testBit_iff`.

## Blockers

Stacked on the conformance PR.
