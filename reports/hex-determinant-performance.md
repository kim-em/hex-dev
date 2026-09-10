# HexDeterminant Performance Report

`HexDeterminant` provides the generic Leibniz-formula determinant and its
cofactor/adjugate/Cauchy-Binet/Plücker theory. Its Phase-4 bench surface is the
combinatorial determinant `Hex.Matrix.det`.

## Bench Targets

- `Hex.DeterminantBench.runLeibnizDet`: `n * leibnizDetComplexity n`

The integer `runLeibnizDet` target has no external comparator: it is the reference
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

The Leibniz path is `O(n · n!)` by construction and is capped at small
dimensions; it is the reference definition, not a performance-critical surface.


## Carrier families

The `runDetDenseInt`, `runDetDenseRat`, `runDetDenseMod`, `runDetMvInt`,
`runDetMvRat`, and `runDetRatFn` families each register five fixed points.
The suffix `_n_size` gives matrix dimension and entry degree or term count.
All registrations hash the entire canonical result; every matched Hex/SymPy
pair agrees. Inputs are prepared outside the timed closures, and SymPy caches
its decoded DomainMatrix after the first request. Timed work includes the
algorithm and canonical output encoding on both sides.

| Input family | Carriers | Dimension sweep | Entry-size sweep |
|---|---|---|---|
| `determinant-dense-carriers` | ZZ[x], QQ[x], GF(101)[x] | 2, 3, 4 at degree 2 | degrees 1, 2, 4 at dimension 3 |
| `determinant-multivariate-carriers` | ZZ[x0,x1,x2], QQ[x0,x1,x2] | 2, 3, 4 at four terms | 2, 4, 8 terms at dimension 3 |
| `determinant-rational-functions` | QQ(x) | 2, 3, 4 at numerator/denominator degree 2 | degrees 1, 2, 4 at dimension 3 |

Dense supports contain no zero coefficients. Multivariate entries have total
degree four and use all three variables even at two terms. Fraction entries
have nonconstant denominators; normalization and cancellation occur in the
Leibniz products and sums. The dimensions keep factorial enumeration small.

## Comparator ratios

**SymPy DomainMatrix.det()** is informational and scheduled-only for these
carrier families. The integer `runLeibnizDet` registration retains its
`structural-layer` comparator-absence declaration.

Measurements use Lean 4.34.0-rc2 and SymPy 1.14.0 on `chungus2`, an AMD EPYC
9455 shared Linux host. Five measured batches per point use a 200 ms minimum
batch duration, with an initial discarded call in each child to start and warm
the persistent Python process. Adjacent Hex/SymPy arms alternate order between
sweep points. The benchmark uses the existing lean-bench fixed-run schedule;
these fixed comparisons assert no asymptotic verdict and gate no Phase-4 goal.

Raw repeats and full-result hashes are in
[the carrier export](bench-results/hex-determinant-carriers.json).
[The context record](bench-results/hex-determinant-carriers-context.json)
records CPU affinity, host load before and after, the exact command, and source
hashes. Additional completed measurements are retained in
[the supplementary export](bench-results/hex-determinant-carriers-initial.json),
with their distinct affinity and support settings in the context record.

Ratios are Hex/SymPy, so values above one mean Hex takes longer. The adjusted
ratio is `Hex / (SymPy - overhead)`, using the median trivial-request cost.
This subtracts constant framing and dispatch only: matrix-request parsing and
result serialization still scale with payload size. Python startup and matrix
preparation are excluded by warmup. Absolute timings remain host observations.

The trivial request median is **5.735 µs** on CPU 14.

| Family | n | Degree / terms | Hex (µs) | SymPy (µs) | Raw ratio | Adjusted ratio |
|---|---:|---:|---:|---:|---:|---:|
| DenseInt | 2 | 2 | 4.447 | 35.149 | 0.13× | 0.15× |
| DenseInt | 3 | 1 | 14.222 | 143.112 | 0.10× | 0.10× |
| DenseInt | 3 | 2 | 11.835 | 123.813 | 0.10× | 0.10× |
| DenseInt | 3 | 4 | 37.284 | 349.506 | 0.11× | 0.11× |
| DenseInt | 4 | 2 | 38.437 | 352.940 | 0.11× | 0.11× |
| DenseRat | 2 | 2 | 22.322 | 75.431 | 0.30× | 0.32× |
| DenseRat | 3 | 1 | 37.678 | 116.378 | 0.32× | 0.34× |
| DenseRat | 3 | 2 | 121.884 | 186.601 | 0.65× | 0.67× |
| DenseRat | 3 | 4 | 171.639 | 324.979 | 0.53× | 0.54× |
| DenseRat | 4 | 2 | 427.499 | 506.546 | 0.84× | 0.85× |
| DenseMod | 2 | 2 | 4.719 | 34.339 | 0.14× | 0.16× |
| DenseMod | 3 | 1 | 14.051 | 86.718 | 0.16× | 0.17× |
| DenseMod | 3 | 2 | 12.993 | 121.518 | 0.11× | 0.11× |
| DenseMod | 3 | 4 | 25.869 | 209.639 | 0.12× | 0.13× |
| DenseMod | 4 | 2 | 46.836 | 335.201 | 0.14× | 0.14× |
| MvInt | 2 | 4 | 34.737 | 78.364 | 0.44× | 0.48× |
| MvInt | 3 | 2 | 54.497 | 154.733 | 0.35× | 0.37× |
| MvInt | 3 | 4 | 246.656 | 270.851 | 0.91× | 0.93× |
| MvInt | 3 | 8 | 1526.161 | 1657.365 | 0.92× | 0.92× |
| MvInt | 4 | 4 | 3213.214 | 934.463 | 3.44× | 3.46× |
| MvRat | 2 | 4 | 57.481 | 93.705 | 0.61× | 0.65× |
| MvRat | 3 | 2 | 93.060 | 130.383 | 0.71× | 0.75× |
| MvRat | 3 | 4 | 377.318 | 378.611 | 1.00× | 1.01× |
| MvRat | 3 | 8 | 2408.658 | 1376.251 | 1.75× | 1.76× |
| MvRat | 4 | 4 | 3005.386 | 1321.093 | 2.27× | 2.28× |
| RatFn | 2 | 2 | 381.677 | 445.041 | 0.86× | 0.87× |
| RatFn | 3 | 1 | 962.549 | 1255.231 | 0.77× | 0.77× |
| RatFn | 3 | 2 | 3276.588 | 1707.593 | 1.92× | 1.93× |
| RatFn | 3 | 4 | 26011.022 | 2706.299 | 9.61× | 9.63× |
| RatFn | 4 | 2 | 33523.011 | 5000.427 | 6.70× | 6.71× |
