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
hashes. Completed supplementary measurements remain in the
[calibration export](bench-results/hex-determinant-carriers-calibration.json)
and [its context](bench-results/hex-determinant-carriers-calibration-context.json),
and in the [initial export](bench-results/hex-determinant-carriers-initial.json).
The calibration export uses the same inputs, with expected-hash assertions
unset and per-request matrix JSON parsing included. The headline table uses
only the current export; supplementary timings have different measurement
settings and must not be pooled. The initial export is unpinned and its multivariate supports differ:
they enumerate degree-four triples before the two mixed triples were placed
first. Its multivariate rows must not be pooled with the current family.

Ratios are Hex/SymPy, so values above one mean Hex takes longer. The adjusted
ratio is `Hex / (SymPy - overhead)`, using the median trivial-request cost.
This subtracts constant framing and dispatch only. Python result serialization
and Lean-side response parsing and recompression still scale with output size;
request-string hashing and cache lookup scale with request size. Matrix decoding
is cached, and startup and matrix preparation are excluded by warmup. Absolute
timings remain host observations.

The trivial request median is **5.012 µs** on CPU 12.

| Family | n | Degree / terms | Hex (µs) | SymPy (µs) | Raw ratio | Adjusted ratio |
|---|---:|---:|---:|---:|---:|---:|
| DenseInt | 2 | 2 | 4.538 | 32.723 | 0.14× | 0.16× |
| DenseInt | 3 | 1 | 7.630 | 83.956 | 0.09× | 0.10× |
| DenseInt | 3 | 2 | 11.642 | 120.806 | 0.10× | 0.10× |
| DenseInt | 3 | 4 | 21.898 | 209.436 | 0.10× | 0.11× |
| DenseInt | 4 | 2 | 37.561 | 341.689 | 0.11× | 0.11× |
| DenseRat | 2 | 2 | 15.540 | 43.174 | 0.36× | 0.41× |
| DenseRat | 3 | 1 | 36.289 | 111.070 | 0.33× | 0.34× |
| DenseRat | 3 | 2 | 71.209 | 166.589 | 0.43× | 0.44× |
| DenseRat | 3 | 4 | 170.899 | 308.802 | 0.55× | 0.56× |
| DenseRat | 4 | 2 | 421.493 | 486.184 | 0.87× | 0.88× |
| DenseMod | 2 | 2 | 4.734 | 32.132 | 0.15× | 0.17× |
| DenseMod | 3 | 1 | 8.173 | 83.164 | 0.10× | 0.10× |
| DenseMod | 3 | 2 | 13.003 | 116.771 | 0.11× | 0.12× |
| DenseMod | 3 | 4 | 25.928 | 202.381 | 0.13× | 0.13× |
| DenseMod | 4 | 2 | 47.212 | 332.051 | 0.14× | 0.14× |
| MvInt | 2 | 4 | 34.068 | 64.150 | 0.53× | 0.58× |
| MvInt | 3 | 2 | 36.270 | 96.428 | 0.38× | 0.40× |
| MvInt | 3 | 4 | 245.111 | 264.484 | 0.93× | 0.94× |
| MvInt | 3 | 8 | 1373.114 | 919.813 | 1.49× | 1.50× |
| MvInt | 4 | 4 | 2051.699 | 910.668 | 2.25× | 2.27× |
| MvRat | 2 | 4 | 54.152 | 83.809 | 0.65× | 0.69× |
| MvRat | 3 | 2 | 67.093 | 123.423 | 0.54× | 0.57× |
| MvRat | 3 | 4 | 363.673 | 357.523 | 1.02× | 1.03× |
| MvRat | 3 | 8 | 1885.348 | 1324.526 | 1.42× | 1.43× |
| MvRat | 4 | 4 | 2985.730 | 1297.226 | 2.30× | 2.31× |
| RatFn | 2 | 2 | 381.381 | 439.893 | 0.87× | 0.88× |
| RatFn | 3 | 1 | 966.739 | 1250.170 | 0.77× | 0.78× |
| RatFn | 3 | 2 | 3269.329 | 1696.204 | 1.93× | 1.93× |
| RatFn | 3 | 4 | 26486.119 | 2690.814 | 9.84× | 9.86× |
| RatFn | 4 | 2 | 33735.498 | 4997.504 | 6.75× | 6.76× |
