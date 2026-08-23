# hex-primality: conformance fixtures and the PARI oracle

## Accomplished

- Three new fixture kinds landed in the shared surface: `isprime`,
  `certcheck` (certificate as a raw JSON object; serializer in the
  emitting driver, since hex-test-kit cannot depend on HexPrimality),
  and `segment`, with emitters in `Hex/Conformance/Emit.lean` (plus
  `boolValue`) and validation incl. a recursive certificate validator
  in `scripts/oracle/common.py`.
- `conformance/HexPrimality/EmitFixtures.lean`: the SPEC's full case
  list (edges, prime squares, near-root semiprimes, all six Carmichael
  numbers, the four base-specific strong pseudoprimes, Fermat primes,
  table/trial/certificate-tier verdicts incl. 2^31 ± something, one
  accepted certificate per node kind incl. cube-root, one hand-built
  rejection per checker condition, segments incl. the
  table-boundary straddle, and the migrated hotPathCandidates window
  pinning view contents and order).
- `conformance/HexPrimality/Conformance.lean` per the testing.md
  module contract; `scripts/oracle/primality_pari.py` (PARI verdicts
  and segments, python-flint second opinion where available, and an
  independent Python replay of the checker whose small leaf uses the
  table's proven semantics); `ORACLES` tuple, lakefile targets, CI
  build-list additions; committed 96-record snapshot.
- Local validation without cypari2: schema-validated via common.py,
  every result cross-checked against a pure-python Miller-Rabin
  stand-in plus the oracle's own certificate replay (48/48 agree),
  and emission verified byte-identical across runs.

## Current frontier

Conformance surface complete pending CI's real-PARI run. Remaining:
bench (PR18) and the sieve (PR4/PR5).

## Next step

PR18: bench families and the phase4 block.

## Blockers

Stacked on the norm_num PR.
