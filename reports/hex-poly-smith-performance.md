# HexPolySmith performance report

`HexPolySmith` computes Smith normal form over dense univariate polynomials,
with optional unimodular transforms, invariant-factor projections,
linear-system solving, a diagonal convenience surface, and direct or
evaluation-based certificate checking.

Measurements were made on `chungus2` (AMD EPYC 9455, 96 logical CPUs,
x86_64, NixOS 26.11, Linux 6.12.100) with Lean 4.34.0-rc2 and lean-bench
0.1.0. The source commit was
`508ff228ddd14528da6427d3ea569bd8f41ca1c1`; the worktree contained this
release implementation. The benchmark source SHA-256 is
`8847c78958d41004ddb606205cb679b79c682afe375020b0fec5a85f1f072fe4`.

The scientific artifact is
[`hex-poly-smith-508ff228-scientific.json`](bench-results/hex-poly-smith-508ff228-scientific.json)
(SHA-256 `6d2230315c57eadb1bca5984f162f69ca947bfe65cdbd0037d2953a91d538931`).
The fixed-comparator artifact is
[`hex-poly-smith-536d29bb-comparators.json`](bench-results/hex-poly-smith-536d29bb-comparators.json)
(SHA-256 `5e58281d91fda2b13f7be9caac9b7db12dbb821fd9701a6944db18cf5861a90b`).
The comparator artifact remains valid because its five prepared families were
preserved unchanged as fixed stress inputs.

The declared performance families are `dense-polysmith`,
`chain-conjugate-poly`, `rational-polysmith`, `diagonal-polysmith`, and
`small-field-degree`.

## Bench targets

Let `L(bits) = (bits + 63) / 64`. These formulas are copied from the
adjacent `setup_benchmark` registrations in
`bench/HexPolySmith/Bench.lean`:

- `dimensionCost n = n^3 * L(8 + Nat.log2 (n + 1))`
- `degreeCost d = D^2 + D * L(4*(d+1))`, where `D = 3*d + 1`
- `rationalDegreeCost d = D^2*k + D*L(3*(d+1)*(k+1))`, where
  `D = 3*d + 1` and `k = Nat.log2 (d+1) + 1`
- `chainCost n = n^3`
- `smallFieldCost d = (3*d + 1)^2`
- `directCertCost n = (n + 1)^4`
- `evaluationCertCost n = (3*n + 2) * (n + 1)^3`

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
| `runInvariantFactors` | `dimensionCost n` |
| `runModuleStructure` | `dimensionCost n` |
| `runQuotientOrder` | `dimensionCost n` |
| `runSolveSystem` | `dimensionCost n` |
| `runDirectProductCert` | `directCertCost n` |
| `runEvaluationCert` | `evaluationCertCost n` |

The models are derived from the registered families, not fitted to observed
wall times. The dense, rational, and small-field degree ladders use consecutive
continuants. Their first two factors force a linear Euclidean remainder chain,
and the third is their product, so the Smith factors remain controlled without
short-circuiting the gcd/division phase. The recurrence bounds final transform
degree by `3*d`; its binomial sums and rational denominator powers give the
coefficient-width terms above. Fixed-degree dimension chains supplement this
Euclidean evidence by isolating dense matrix traversal.

The per-library SPEC separately retains the general operational worst-case
bound in terms of total reductions, maximum intermediate degree, and maximum
coefficient-limb width. These two-sided family models specialize that bound;
they do not replace it.

Direct certification uses dense degree-linear unimodular witnesses. Its matrix
dot products perform cubic cells of degree-linear polynomial scans, including
`acc + 0`, giving the quartic model. Evaluation certification checks exactly
`3*n + 2` points and performs cubic scalar work at each point.

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
`runDirectProductCert` retains its quartic bound but now uses dense
degree-linear witnesses that exercise the polynomial scans omitted by the old
sparse small-rung family; its extended schedule reaches `n = 96` with
`beta = -0.121`. `runDiagonalSnf` keeps the unordered presentation that forces
`badBlock` and `blockStep`, and extends the schedule to `n = 768`; its
independent cubic model passes with `beta = -0.065`.

The fixed comparator endpoints and canonical expected-hash checks make no
complexity claim, have no mode, and do not replace these sixteen performance
registrations.

`C` is per-call time divided by the declared model over the verdict window.
The last column is the largest completed rung. Every registration has a fitted
residual slope; none relies on the narrow-window fallback or a cap-truncated
rung.

| target | verdict | C min | C max | β | max rung |
|---|---|---:|---:|---:|---:|
| `runDenseSnfDimension` | consistent with declared complexity | 1374.329 | 1461.170 | -0.032 | 128 |
| `runDenseSnfDataDimension` | consistent with declared complexity | 1507.405 | 1668.436 | -0.049 | 128 |
| `runDenseSnfDegree` | consistent with declared complexity | 7493.632 | 8139.356 | +0.035 | 128 |
| `runDenseSnfDataDegree` | consistent with declared complexity | 10277.149 | 10614.714 | +0.008 | 128 |
| `runChainSnf` | consistent with declared complexity | 782.998 | 936.093 | -0.126 | 32 |
| `runRationalSnfDataDimension` | consistent with declared complexity | 1484.929 | 1621.102 | -0.052 | 128 |
| `runRationalSnfDataDegree` | consistent with declared complexity | 3501.352 | 4790.906 | +0.123 | 128 |
| `runDiagonalSnf` | consistent with declared complexity | 29.672 | 34.090 | -0.065 | 768 |
| `runSmallField` | consistent with declared complexity | 226.268 | 234.991 | -0.023 | 256 |
| `runSnfRank` | consistent with declared complexity | 1366.166 | 1459.192 | -0.026 | 128 |
| `runInvariantFactors` | consistent with declared complexity | 1375.613 | 1446.843 | -0.033 | 128 |
| `runModuleStructure` | consistent with declared complexity | 2759.168 | 3029.545 | -0.023 | 128 |
| `runQuotientOrder` | consistent with declared complexity | 2856.060 | 3139.850 | -0.046 | 128 |
| `runSolveSystem` | consistent with declared complexity | 1510.575 | 1639.465 | -0.055 | 128 |
| `runDirectProductCert` | consistent with declared complexity | 168.291 | 216.363 | -0.121 | 96 |
| `runEvaluationCert` | consistent with declared complexity | 332.215 | 343.167 | -0.002 | 48 |

The growth diagnostic runs `snfData` and measures the input, diagonal, and all
four final transform matrices. At degree 64, the dense and rational
consecutive-remainder families both reach boundary degree 192, with 240-bit
and 1346-bit coefficients respectively. These agree with the independently
derived `3*d`, `4*(d+1)`, and rational denominator-power bounds. The dimension
ladders keep degree fixed at four while coefficient width grows
logarithmically with matrix size. The exact
output of
`.lake/build/bin/hexpolysmith_bench growth` is
[`hex-poly-smith-growth.csv`](bench-results/hex-poly-smith-growth.csv)
(SHA-256 `39cd5f718dd243b80ceb376d379a2bccf05789737c8577cea50edd4e352469dc`).

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

One representative compiled case was sampled for every currently declared
input family at 999 Hz with samply 0.13.1 and lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Raw filtered profiles and symbol
sidecars are developer-local under `/tmp`. The categorizer SHA-256 is
`8c0df4b121c222114464683b6f7716b74a1e15070a2320c05026b273c61b703f`.

| family / target / parameter | own | GMP | allocation | Lean runtime | other | classified |
|---|---:|---:|---:|---:|---:|---:|
| dense / `runDenseSnfDegree`, `degree=128` | 0.13% | 32.98% | 54.99% | 11.87% | 0.03% | 99.97% |
| chain / `runChainSnf`, `n=32` | 5.02% | 27.91% | 40.88% | 25.04% | 1.14% | 98.86% |
| rational / `runRationalSnfDataDegree`, `degree=64` | 0.07% | 49.02% | 41.68% | 9.24% | 0.00% | 100.00% |
| diagonal / `runDiagonalSnf`, `n=384` | 24.40% | 0.84% | 22.73% | 51.73% | 0.30% | 99.70% |
| small field / `runSmallField`, `degree=256` | 9.88% | 0.00% | 25.24% | 64.70% | 0.18% | 99.82% |

Dominant inclusive costs are attributable to the registered paths:

- Dense: `smithLoopTotal` 98.12%, `smithStage` 98.01%,
  `clearColumnScan` 97.65%, `DensePoly.mulImpl` 79.46%, and
  `DensePoly.xgcd` 13.09%.
- Chain: `smithLoopTotal` 99.04%, `smithStage` 96.65%,
  `clearColumnScan` 43.10%, and `DensePoly.divMod` 40.77%.
- Rational: `snfData` and `smithLoopTotal` 85.52%, `smithStage` 85.38%,
  `DensePoly.mulImpl` 71.77%, and `mapTransforms` 19.86%.
- Diagonal: `snfDiagonal` and `smithLoopTotal` 74.46%,
  `smithStage` 56.44%, `badBlockEntry` 30.85%, and
  `trailingRowStep` 17.72%.
- Small field: `snfData` and `smithLoopTotal` 99.96%,
  `smithStage` 99.91%, `clearColumnScan` 99.56%, and
  `DensePoly.mulImpl` 93.36%.

All five profiles passed calibration, sensitivity, and confidence checks.
Residuals were 0.757–0.994 ms; retained sample counts were 1673–3826. The exact
commands used `scripts/profile/run_profile.sh`, the target and parameter shown
in the table, and a 3,000,000,000 ns target duration.

## Concerns

No open Phase-4 performance concern remains. Every parametric registration
passes mode 1 with a model derived from its controlled family, and the
fixed-comparator corpus still checks the original hard families without
promoting their timings into complexity claims. The current dense, rational,
small-field, and diagonal profiles show that the consecutive-remainder and
block-repair phases are exercised, so the supplemental divisibility chains are
not sole short-circuit evidence. `HexPolySmith.done_through` is therefore
restored to 4 under the ordered-mode policy in
[#9733](https://github.com/kim-em/hex-dev/issues/9733).
