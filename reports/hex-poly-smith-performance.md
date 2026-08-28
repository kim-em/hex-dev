# HexPolySmith performance report

`HexPolySmith` computes Smith normal form over dense univariate polynomials,
with optional unimodular transforms, invariant-factor projections,
linear-system solving, a diagonal convenience surface, and direct or
evaluation-based certificate checking.

Measurements were made on `chungus2` (AMD EPYC 9455, 96 logical CPUs,
x86_64, NixOS 26.11, Linux 6.12.100) with Lean 4.34.0-rc2 and lean-bench
0.1.0. The source commit was
`ebae1ba7767b9a86ca31a65d77ff8854445d0971`; the worktree contained this
release implementation. The benchmark source SHA-256 is
`77384e9dabdd192b7d89a380c3eecfa1c4c45d1a7155dbb9ff9f0e4411494db5`.

The scientific artifact is
[`hex-poly-smith-ebae1ba7-scientific.json`](bench-results/hex-poly-smith-ebae1ba7-scientific.json)
(SHA-256 `2e97b0ed1480f4b43a62556d3b7fde73802a59180a7565c60ff1d8fbce4436eb`).
The fixed-comparator artifact is
[`hex-poly-smith-536d29bb-comparators.json`](bench-results/hex-poly-smith-536d29bb-comparators.json)
(SHA-256 `5e58281d91fda2b13f7be9caac9b7db12dbb821fd9701a6944db18cf5861a90b`).
The comparator artifact remains valid because its five prepared families were
preserved unchanged as fixed stress inputs.

The declared performance families are `dense-chain-polysmith`,
`chain-conjugate-poly`, `rational-chain`, `diagonal-chain`, and
`small-field-degree`.

## Bench targets

Let `L(bits) = (bits + 63) / 64`. These formulas are copied from the
adjacent `setup_benchmark` registrations in
`bench/HexPolySmith/Bench.lean`:

- `dimensionCost n = n^3 * L(8 + Nat.log2 (n + 1))`
- `degreeCost d = (2*d + 1)^2 * L(12 + Nat.log2 (d + 1))`
- `rationalDegreeCost d = (2*d + 1)^2 * L(2*(Nat.log2 (d + 1) + 1) + 1)`
- `chainCost n = n^3`
- `gradedChainCost n = n^4`
- `smallFieldCost d = (2*d + 1)^2`
- `directCertCost n = n^3`
- `evaluationCertCost n = (n + 1)^4`

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
| `runSmallField` | `smallFieldCost degree` |
| `runSnfRank` | `dimensionCost n` |
| `runInvariantFactors` | `gradedChainCost n` |
| `runModuleStructure` | `dimensionCost n` |
| `runQuotientOrder` | `dimensionCost n` |
| `runSolveSystem` | `dimensionCost n` |
| `runDirectProductCert` | `directCertCost n` |
| `runEvaluationCert` | `evaluationCertCost n` |

The models are derived from the registered families, not fitted to observed
wall times. Dense and rational registrations use invariant-factor chains with
factors `p`, `p^2`, ..., so exact divisibility removes the uncontrolled
coprime-family Euclidean swell. Their maximum degree, denominator width, and
bounded-coefficient sums give the degree and limb factors above. The graded
chain has factor degrees `1, ..., n`, hence one additional degree factor. The
small-field family fixes dimension at three and varies the degrees of `x^d`
and `x^(2*d)`.

The direct certificate model is separately corrected from quartic to cubic:
only quadratically many products have nonzero polynomial operands, while the
remaining dense scan is cubic. Evaluation certification retains a quartic
model because it evaluates at linearly many points and performs cubic scalar
matrix work at each point.

There are also 76 fixed registrations: one persistent-process overhead probe
and, for every one of five input families at five canonical rungs, one Lean,
one SymPy, and one PARI call. Each uses five measured repeats, an 8 s cap, and
at least 0.1 s of auto-tuned inner calls per repeat.

Each scientific registration was run in a fresh benchmark process to avoid
cross-target thermal and load coupling, then the results were combined by
fully qualified function name into the scientific artifact. The per-target
command shape was:

```sh
.lake/build/bin/hexpolysmith_bench run \
  Hex.PolySmithBench.<registration> \
  --export-file /tmp/<registration>.json
```

## Verdicts

All sixteen parametric performance registrations pass **mode 1, two-sided
parametric** with their declared, family-derived wall models. The controlled
families preserve stable parametric ladders while including their maximum
polynomial degree and rational coefficient width. No model was selected by
fitting observations.

The two previously separate failures have separate resolutions.
`runDirectProductCert` now declares the cubic work performed by its sparse
prepared transforms; evaluation certification remains quartic.
`runDiagonalSnf` uses an ordered diagonal chain, for which every pivot divides
the trailing block and `badBlock` scans the full quadratic remainder at each
stage. Its schedule now reaches `n = 768`; excluding the fixed-cost transition
rungs yields `beta = -0.046`, comfortably inside the mode-1 tolerance.

The fixed comparator endpoints and canonical expected-hash checks make no
complexity claim, have no mode, and do not replace these sixteen performance
registrations.

`C` is per-call time divided by the declared model over the verdict window.
The last column is the largest completed rung; `—` means the window contains
too few residual points for a slope fit, while the bounded `C` ratio still
satisfies the declared mode.

| target | verdict | C min | C max | β | max rung |
|---|---|---:|---:|---:|---:|
| `runDenseSnfDimension` | consistent with declared complexity | 2721.633 | 3472.796 | +0.146 | 128 |
| `runDenseSnfDataDimension` | consistent with declared complexity | 3057.014 | 3826.213 | +0.135 | 128 |
| `runDenseSnfDegree` | consistent with declared complexity | 2611.600 | 3438.238 | -0.128 | 128 |
| `runDenseSnfDataDegree` | consistent with declared complexity | 2629.560 | 3232.708 | — | 128 |
| `runChainSnf` | consistent with declared complexity | 1506.377 | 1720.764 | -0.105 | 32 |
| `runRationalSnfDataDimension` | consistent with declared complexity | 3112.878 | 3657.965 | +0.104 | 128 |
| `runRationalSnfDataDegree` | consistent with declared complexity | 2869.976 | 3434.496 | -0.082 | 64 |
| `runDiagonalSnf` | consistent with declared complexity | 30.632 | 32.503 | -0.046 | 768 |
| `runSmallField` | consistent with declared complexity | 25.709 | 30.633 | -0.098 | 256 |
| `runSnfRank` | consistent with declared complexity | 1764.378 | 2522.052 | -0.017 | 128 |
| `runInvariantFactors` | consistent with declared complexity | 480.898 | 654.336 | -0.036 | 32 |
| `runModuleStructure` | consistent with declared complexity | 3218.910 | 4391.216 | -0.009 | 128 |
| `runQuotientOrder` | consistent with declared complexity | 3537.210 | 4436.427 | -0.106 | 128 |
| `runSolveSystem` | consistent with declared complexity | 1722.615 | 1933.533 | -0.064 | 128 |
| `runDirectProductCert` | consistent with declared complexity | 2298.181 | 3137.433 | — | 32 |
| `runEvaluationCert` | consistent with declared complexity | 1167.890 | 1603.651 | — | 32 |

The growth diagnostic runs `snfData` and measures the input, diagonal, and all
four final transform matrices. At the largest exported degree rung, the dense
and rational chains both reach degree 128 with 14-bit and 15-bit rational
coefficients respectively; the exact model factors come from the construction
rather than these observations. The dimension ladders keep degree fixed at
four while coefficient width grows logarithmically with matrix size. The exact
output of
`.lake/build/bin/hexpolysmith_bench growth` is
[`hex-poly-smith-growth.csv`](bench-results/hex-poly-smith-growth.csv)
(SHA-256 `bb5782fa224897231e5239d80873b969c6d64472d6a68d4e3d715da2a3d24ea8`).

All 75 implementation calls in the fixed artifact agreed within their five
repeats. Every Lean/SymPy/PARI triple produced the same observed hash at every
canonical input; no call timed out or hit its cap. These fixed inputs are the
original generic dense, rational, diagonal, chain, and small-field stress
cases, retained independently from the controlled performance families.
The separate 92-target `verify` run passed in the declared SymPy/PARI
environment.

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

The profiles below are the diagnostic samples from source commit `536d29bb`.
They establish the original finding that GMP-backed coefficient work and
allocation dominated the uncontrolled dense and rational stress families;
they are retained as root-cause evidence, not used to validate the replacement
mode-1 models. One representative compiled case was sampled for each old input
family at 999 Hz with samply 0.13.1 and lean-bench-samply commit
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

All five historical profiles passed calibration, sensitivity, and confidence
checks.
Residuals were 0.512–0.984 ms; retained sample counts were 1699–3675. The exact
commands used `scripts/profile/run_profile.sh`, the target and parameter shown
in the table, and a 3,000,000,000 ns target duration.

## Concerns

No open Phase-4 performance concern remains. Every parametric registration
passes mode 1 with a model derived from its controlled family, and the
fixed-comparator corpus still checks the original hard families without
promoting their timings into complexity claims. The historical profiles remain
useful evidence that those generic inputs exhibit expression swell; this
remediation avoids claiming a scalar model for them rather than fitting that
swell after observation. `HexPolySmith.done_through` is therefore restored to
4 under the ordered-mode policy in
[#9733](https://github.com/kim-em/hex-dev/issues/9733).
