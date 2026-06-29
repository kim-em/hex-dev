# HexDeterminant Performance Report

`HexDeterminant` provides the generic Leibniz-formula determinant and its
cofactor/adjugate/Cauchy-Binet/Plücker theory. Its Phase-4 bench surface is the
combinatorial determinant `Hex.Matrix.det`.

## Bench Targets

- `Hex.DeterminantBench.runLeibnizDet`: `n * leibnizDetComplexity n`

The Leibniz determinant has no external comparator: it is the reference
combinatorial definition (signed sum over `n!` permutations), cross-checked for
agreement against the row-pivoted Bareiss determinant in `hex-bareiss` rather
than against an external tool (declared absence with the `structural-layer`
reason per `SPEC/Libraries/hex-determinant.md §"External comparators"`).

## Verdicts

Measured on `carica` (Apple M2 Ultra, macOS 14.6.1). The
`leibniz-small-determinant` figures below were captured under the pre-split
consolidated `hexmatrix_bench` driver and are unchanged by the library split
(the timed `Hex.Matrix.det` surface is identical).

- `Hex.DeterminantBench.runLeibnizDet`
  - Command: `lake exe hexdeterminant_bench run Hex.DeterminantBench.runLeibnizDet`
  - Input family: `leibniz-small-determinant`; deterministic salt `71`;
    parameters `2, 3, 4, 5, 6, 7, 8`.
  - Per-call times: `≤1 µs`, `1.957 µs`, `8.424 µs`, `47.000 µs`,
    `321.418 µs`, `2.566 ms`, `23.174 ms`.
  - Verdict: consistent with declared complexity (`cMin=71.843`,
    `cMax=78.334`, `β=—`).

A within-Lean determinant cross-check confirms `Hex.Matrix.det` agrees with the
row-pivoted Bareiss determinant on the common parameter domain; the executable
agreement is also exercised by the `hex-bareiss` conformance oracle (the
`bareiss` op is expected to equal the combinatorial `det` on every fixture).

## Profile

Profile captured on `carica` through the bench-timed-region filtering wrapper.

- `leibniz-small-determinant`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexdeterminant_bench Hex.DeterminantBench.runLeibnizDet 8 5000000000`
  - Leaf cost: Lean runtime and harness 57.5%, Lean own code 20.9%,
    allocation/free 17.4%, other system samples 4.2%, with no visible GMP
    leaf share on this small structured determinant.
  - Inclusive ranking: `Hex.DeterminantBench.runLeibnizDet` and its wrapper
    covered 100.0% of retained samples, the Leibniz determinant fold covered
    55.7%, `detTerm` covered 54.5%, `permutationVectors` construction covered
    43.0% / 38.9%, `detSign` covered 29.9%, and `inversionCount` covered 15.3%.
    These are the expected factorial permutation/enumeration costs.

The dominant inclusive costs all map to the registered `HexDeterminant.Bench`
target. No unattributed dominant cost was observed.

## Concerns

None. The Leibniz path is `O(n · n!)` by construction and is capped at small
dimensions; it is the reference definition, not a performance-critical surface.
