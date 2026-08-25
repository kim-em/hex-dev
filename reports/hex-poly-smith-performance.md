# HexPolySmith performance report

`HexPolySmith` computes Smith normal form over dense univariate polynomials,
with optional unimodular transforms, invariant-factor projections,
linear-system solving, a diagonal convenience surface, and direct or
evaluation-based certificate checking.

Measurements were made on `chungus2` (AMD EPYC 9455, 96 logical CPUs,
x86_64, NixOS 26.11, Linux 6.12.100) with Lean 4.34.0-rc2 and lean-bench
0.1.0. The source commit was
`536d29bbf88e491c8e5b9a21484647c15f44a365`; the worktree contained this
release implementation. The benchmark source SHA-256 is
`af13d1cdfce08ff5014b6efe3fc92e4ef37a72cf1f7acf54a7b3657aca0f375a`.

The scientific artifact is
[`hex-poly-smith-536d29bb-scientific.json`](bench-results/hex-poly-smith-536d29bb-scientific.json)
(SHA-256 `202ee28a901d47a6989650691d553c812a2a1c6193e87eac8b90b352e25f766a`).
The fixed-comparator artifact is
[`hex-poly-smith-536d29bb-comparators.json`](bench-results/hex-poly-smith-536d29bb-comparators.json)
(SHA-256 `5e58281d91fda2b13f7be9caac9b7db12dbb821fd9701a6944db18cf5861a90b`).

## Bench targets

These formulas are copied from the adjacent `setup_benchmark` registrations
in `bench/HexPolySmith/Bench.lean`:

- `dimensionCost n = n * n * n`
- `degreeCost degree = (degree + 1) * (degree + 1)`
- `rationalDegreeCost degree = degreeCost degree * (Nat.log2 (degree + 1) + 1)`
- `chainCost n = n * n * n`
- `certDimensionCost n = ((n + 1) * (n + 1))^2`

| target | declared complexity |
|---|---|
| `runDenseSnfDimension` | `dimensionCost n` |
| `runDenseSnfDataDimension` | `dimensionCost n` |
| `runDenseSnfDegree` | `degreeCost degree` |
| `runDenseSnfDataDegree` | `degreeCost degree` |
| `runChainSnf` | `chainCost n` |
| `runRationalSnfDataDimension` | `dimensionCost n` |
| `runRationalSnfDataDegree` | `rationalDegreeCost degree` |
| `runDiagonalSnf` | `dimensionCost n` |
| `runSmallField` | `dimensionCost n` |
| `runSnfRank` | `dimensionCost n` |
| `runInvariantFactors` | `dimensionCost n` |
| `runModuleStructure` | `dimensionCost n` |
| `runQuotientOrder` | `dimensionCost n` |
| `runSolveSystem` | `dimensionCost n` |
| `runDirectProductCert` | `certDimensionCost n` |
| `runEvaluationCert` | `certDimensionCost n` |

The dimension and degree formulas are algebraic-operation proxies. The
separate boundary-growth artifact deliberately keeps intermediate polynomial
degree and rational coefficient width visible instead of building an
input-specific empirical fit into those formulas.

There are also 76 fixed registrations: one persistent-process overhead probe
and, for every one of five input families at five canonical rungs, one Lean,
one SymPy, and one PARI call. Each uses five measured repeats, an 8 s cap, and
at least 0.1 s of auto-tuned inner calls per repeat.

Scientific command:

```sh
.lake/build/bin/hexpolysmith_bench run \
  Hex.PolySmithBench.runDenseSnfDimension \
  Hex.PolySmithBench.runDenseSnfDataDimension \
  Hex.PolySmithBench.runDenseSnfDegree \
  Hex.PolySmithBench.runDenseSnfDataDegree \
  Hex.PolySmithBench.runChainSnf \
  Hex.PolySmithBench.runRationalSnfDataDimension \
  Hex.PolySmithBench.runRationalSnfDataDegree \
  Hex.PolySmithBench.runDiagonalSnf \
  Hex.PolySmithBench.runSmallField \
  Hex.PolySmithBench.runSnfRank \
  Hex.PolySmithBench.runInvariantFactors \
  Hex.PolySmithBench.runModuleStructure \
  Hex.PolySmithBench.runQuotientOrder \
  Hex.PolySmithBench.runSolveSystem \
  Hex.PolySmithBench.runDirectProductCert \
  Hex.PolySmithBench.runEvaluationCert \
  --export-file reports/bench-results/hex-poly-smith-536d29bb-scientific.json
```

## Verdicts

`C` is per-call time divided by the declared model. The last column is the
largest completed rung; `—` means the wallclock cap prevented a residual-slope
fit.

| target | verdict | C min | C max | β | max rung |
|---|---|---:|---:|---:|---:|
| `runDenseSnfDimension` | inconclusive | 17260.255 | 4241581.167 | — | 12 |
| `runDenseSnfDataDimension` | inconclusive | 10797.355 | 182028.270 | — | 8 |
| `runDenseSnfDegree` | inconclusive | 54707.213 | 11571275.739 | +2.342 | 24 |
| `runDenseSnfDataDegree` | inconclusive | 85818.462 | 742339.661 | +1.768 | 10 |
| `runChainSnf` | consistent with declared complexity | 782.982 | 952.583 | -0.136 | 32 |
| `runRationalSnfDataDimension` | inconclusive | 14600.040 | 236927.842 | — | 8 |
| `runRationalSnfDataDegree` | inconclusive | 47386.009 | 792574.062 | +2.331 | 10 |
| `runDiagonalSnf` | inconclusive | 30.850 | 40.130 | -0.155 | 256 |
| `runSmallField` | consistent with declared complexity | 71.255 | 85.002 | -0.103 | 256 |
| `runSnfRank` | inconclusive | 17473.289 | 4217294.621 | — | 12 |
| `runInvariantFactors` | inconclusive | 17124.798 | 4203737.110 | — | 12 |
| `runModuleStructure` | inconclusive | 14416.571 | 92356.593 | — | 8 |
| `runQuotientOrder` | inconclusive | 14394.419 | 93098.829 | — | 8 |
| `runSolveSystem` | inconclusive | 12545.480 | 219873.422 | — | 8 |
| `runDirectProductCert` | inconclusive | 74.835 | 220.455 | -0.786 | 16 |
| `runEvaluationCert` | inconclusive | 869.374 | 1283.942 | +0.291 | 16 |

The inconclusive dense-rational verdicts are explained by measured expression
swell, not benchmark noise. At degree 8 the deterministic dense family reaches
boundary degree 37 and 2400-bit coefficients; its nonintegral rational peer
reaches degree 37 and 7203-bit coefficients. In contrast, the chain family
stays at degree 2 and at most 3 coefficient bits, and the small-field family
stays at degree 2. The exact output of
`.lake/build/bin/hexpolysmith_bench growth` is
[`hex-poly-smith-growth.csv`](bench-results/hex-poly-smith-growth.csv)
(SHA-256 `c7f28c5e4883fd2f580c1d087c28853917145ac5029c66747c8a59f581ea3bd6`).

All 75 implementation calls in the fixed artifact agreed within their five
repeats. Every Lean/SymPy/PARI triple produced the same observed hash at every
canonical input; no call timed out or hit its cap. The separate 92-target
`verify` run also passed in the declared SymPy/PARI environment.

## Comparator ratios

The named comparators are **SymPy smith_normal_form over polynomial domains**
and **PARI matsnf on polynomial entries**. The external environment used
SymPy 1.14.0 and cypari2 2.2.4/PARI through the persistent
`scripts/oracle/pari_bench_driver.py` service. The driver SHA-256 is
`80ef9e9fe4fe1d7bfdcdd268279bb3c009219976ce0f4e42d6906fa857ae73be`;
the independent oracle SHA-256 is
`3ba2652d427e2e10b30b9460c5148f0500b15bfd0cd4a128d15e75ed869aabed`.
The persistent-call overhead median was 7.162 µs.

Ratios are `comparator / Lean`, so values above one mean Lean is faster. The
adjusted value subtracts 7.162 µs from the comparator median. All rungs are
eligible: the overhead is at most 50% of each external median, and every call
is far below the 10 s hard ceiling. The comparators are informational because
neither exposes the rectangular transform, solving, structure, or certificate
surfaces.

### `random-dense-polysmith`

| n | Lean µs | SymPy µs | raw / adjusted | PARI µs | raw / adjusted |
|---:|---:|---:|---:|---:|---:|
| 1 | 2.102 | 279.347 | 132.896x / 129.489x | 20.932 | 9.958x / 6.551x |
| 2 | 47.438 | 984.751 | 20.759x / 20.608x | 57.284 | 1.208x / 1.057x |
| 3 | 157.267 | 2093.663 | 13.313x / 13.267x | 138.936 | 0.883x / 0.838x |
| 4 | 460.865 | 4285.999 | 9.300x / 9.284x | 298.755 | 0.648x / 0.633x |
| 5 | 1007.473 | 7582.080 | 7.526x / 7.519x | 609.409 | 0.605x / 0.598x |

Startup effects contract rapidly. SymPy remains 7.5x slower at the largest
rung, while PARI crosses parity at `n = 3` and reaches 0.60x as its
fraction-free polynomial machinery avoids Lean's coefficient swell.

Plot: [`random-dense-polysmith`](figures/hex-poly-smith-comparator-random-dense-polysmith.svg).

### `chain-conjugate-poly`

| n | Lean µs | SymPy µs | raw / adjusted | PARI µs | raw / adjusted |
|---:|---:|---:|---:|---:|---:|
| 1 | 1.772 | 210.347 | 118.706x / 114.664x | 18.789 | 10.603x / 6.562x |
| 2 | 23.373 | 546.318 | 23.374x / 23.067x | 43.752 | 1.872x / 1.565x |
| 3 | 45.779 | 919.037 | 20.076x / 19.919x | 80.038 | 1.748x / 1.592x |
| 4 | 84.400 | 1431.486 | 16.961x / 16.876x | 131.646 | 1.560x / 1.475x |
| 5 | 142.281 | 2151.592 | 15.122x / 15.072x | 195.197 | 1.372x / 1.322x |

Both ratios contract toward constants across the eligible range. PARI is
within 1.32x adjusted at `n = 5`; SymPy remains about 15x slower.

Plot: [`chain-conjugate-poly`](figures/hex-poly-smith-comparator-chain-conjugate-poly.svg).

### `rational-coefficients`

| degree | Lean µs | SymPy µs | raw / adjusted | PARI µs | raw / adjusted |
|---:|---:|---:|---:|---:|---:|
| 1 | 94.035 | 1655.151 | 17.601x / 17.525x | 107.762 | 1.146x / 1.070x |
| 2 | 380.963 | 2689.930 | 7.061x / 7.042x | 158.902 | 0.417x / 0.398x |
| 3 | 1158.759 | 4465.083 | 3.853x / 3.847x | 215.240 | 0.186x / 0.180x |
| 4 | 2749.084 | 6512.640 | 2.369x / 2.366x | 292.132 | 0.106x / 0.104x |
| 5 | 6115.180 | 9915.335 | 1.621x / 1.620x | 395.333 | 0.065x / 0.063x |

SymPy's ratio contracts toward parity. PARI crosses parity at degree 2 and its
advantage grows with the same rational coefficient swell visible in the
boundary artifact. This is the only adverse informational trend, and it
matches the different algorithmic kernels rather than a comparator mismatch.

Plot: [`rational-coefficients`](figures/hex-poly-smith-comparator-rational-coefficients.svg).

### `diagonal-polysmith`

| n | Lean µs | SymPy µs | raw / adjusted | PARI µs | raw / adjusted |
|---:|---:|---:|---:|---:|---:|
| 2 | 4.658 | 377.539 | 81.052x / 79.514x | 33.048 | 7.095x / 5.557x |
| 4 | 13.765 | 719.233 | 52.251x / 51.731x | 72.331 | 5.255x / 4.734x |
| 6 | 28.971 | 1148.641 | 39.648x / 39.401x | 129.163 | 4.458x / 4.211x |
| 8 | 50.937 | 1642.806 | 32.252x / 32.111x | 201.303 | 3.952x / 3.811x |
| 10 | 82.236 | 2212.956 | 26.910x / 26.823x | 296.537 | 3.606x / 3.519x |

Both gaps contract smoothly as fixed costs amortize. The public diagonal
wrapper stays ahead of both external systems at every rung.

Plot: [`diagonal-polysmith`](figures/hex-poly-smith-comparator-diagonal-polysmith.svg).

### `small-field`

| n | Lean µs | SymPy µs | raw / adjusted | PARI µs | raw / adjusted |
|---:|---:|---:|---:|---:|---:|
| 1 | 0.831 | 218.233 | 262.615x / 253.996x | 16.353 | 19.679x / 11.060x |
| 2 | 5.362 | 616.843 | 115.040x / 113.704x | 40.436 | 7.541x / 6.206x |
| 3 | 8.280 | 962.932 | 116.296x / 115.431x | 67.319 | 8.130x / 7.265x |
| 4 | 19.645 | 1592.275 | 81.052x / 80.688x | 132.893 | 6.765x / 6.400x |
| 5 | 27.147 | 2380.780 | 87.700x / 87.436x | 184.402 | 6.793x / 6.529x |

After the startup-heavy first rung, both ratios remain bounded constants with
Lean ahead. The packed `ZMod64 2` path has no rational-coefficient cost.

Plot: [`small-field`](figures/hex-poly-smith-comparator-small-field.svg).

The plots were regenerated from the comparator artifact with
`scripts/plots/hex-poly-smith-comparator.py --family <family>`; the generator
SHA-256 is
`3126664fdb811c37bf0527bb57b6aede23466e3255248b91f8dc977ca095b330`.

## Profile

One representative compiled case was sampled for every declared input family
at 999 Hz with samply 0.13.1 and lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Raw filtered profiles and symbol
sidecars are developer-local under `/tmp`. The categorizer SHA-256 is
`95e4a9642473fe82ca8349724f924d991866f2db40d88921da61f1d98626a6fd`.

| family / target / parameter | own | GMP | allocation | Lean runtime | other | classified |
|---|---:|---:|---:|---:|---:|---:|
| dense / `runDenseSnfDimension`, `n=8` | 0.69% | 43.78% | 41.67% | 13.56% | 0.30% | 99.70% |
| chain / `runChainSnf`, `n=32` | 4.94% | 26.02% | 42.50% | 25.37% | 1.18% | 98.82% |
| rational / `runRationalSnfDataDegree`, `degree=8` | 0.00% | 71.15% | 5.00% | 23.85% | 0.00% | 100.00% |
| diagonal / `runDiagonalSnf`, `n=256` | 18.74% | 1.65% | 13.33% | 66.13% | 0.15% | 99.85% |
| small field / `runSmallField`, `n=256` | 26.80% | 0.00% | 26.75% | 45.12% | 1.33% | 98.67% |

Dominant inclusive costs are attributable to the registered paths:

- Dense: `smithLoopTotal` 98.91%, `smithStage` 98.02%,
  `clearColumnScan` 77.14%, and `DensePoly.mulImpl` 65.56%.
- Chain: `smithLoopTotal` 98.71%, `smithStage` 96.53%,
  `clearColumnScan` 44.38%, and `DensePoly.divMod` 41.08%.
- Rational: `snfData` and `smithLoopTotal` 78.33%, `smithStage` 77.40%,
  `DensePoly.mulImpl` 71.51%, and `mapTransforms` 39.01%.
- Diagonal: `snfDiagonal` 74.64%, `smithLoopTotal` 74.48%,
  `smithStage` 58.39%, and `badBlockEntry` 32.57%.
- Small field: `snfData` 99.59%, `smithLoopTotal` 99.48%,
  `smithStage` 89.93%, and `badBlockEntry` 35.21%.

All five profiles passed calibration, sensitivity, and confidence checks.
Residuals were 0.512–0.984 ms; retained sample counts were 1699–3675. The exact
commands used `scripts/profile/run_profile.sh`, the target and parameter shown
in the table, and a 3,000,000,000 ns target duration.

## Concerns

None. The dense and rational scientific verdicts are intentionally reported as
inconclusive: the boundary-growth artifact and profiles attribute the departure
from algebraic-operation proxies to intermediate degree and coefficient swell
in the classical Euclidean kernel. The external comparators are informational,
all hashes agree, and no unexplained correctness, wiring, or profiling concern
remains.
