# HexPolyFast Performance Report

This report is the Phase-4 audit record for the active, unreleased
`HexPolyFast` library.

The retained scientific comparisons were measured on 2026-08-27 on
`chungus2` (AMD EPYC 9455, Linux x86-64) with Lean `4.34.0-rc2`. Each table
below names the commit that introduced the measurement and gives the exact
command needed to refresh it. Inputs are deterministic and have no random
seed. The accepted scientific export uses clean revision `53ef234e9` pinned
to logical CPU 2; CPU 2 and its SMT sibling 50 were both idle immediately
after the run. The accepted FLINT export uses clean revision `7dac5bd67`, and
the profiles use clean binary revision `d620e128e`.

## Bench targets

The compiled driver is `bench/HexPolyFast/Bench.lean`, built as
`hexpolyfast_bench`. These are the declared models copied from its
registrations.

The division, product/remainder-tree, multipoint, interpolation, and Padé
scientific fixtures use `ZMod64 65537`. This fixed-width prime field makes the
registered coefficient-operation models observable without conflating them
with growing integer numerators or rational denominators. The historical
exact-arithmetic crossover cells below remain evidence for route selection;
they answer a different question from these unit-cost asymptotic ladders.

`karatsubaCost n` is the finite-range recurrence used by every registration
that invokes the cutoff-32 plan: it is `n²` through 32 and
`3 * karatsubaCost ((n + 1) / 2) + n` above it. This is asymptotically
`Θ(n^(log₂ 3))` and, unlike the former `n * sqrt n` proxy, models the retained
31/32/33 transition rows directly.

### Full-and-clipped multiplication

- `runSchoolbook`: `n ^ 2`
- `runSchoolbookList`: `n ^ 2`
- `runSchoolbookLoop`: `n ^ 2`
- `runKaratsuba`: `karatsubaCost n`
- `runKaratsubaSquare`: `karatsubaCost n`
- `runKaratsubaSkew`: `karatsubaCost n`
- `runBlocksTail`: `karatsubaCost n`
- `runBlocksOffset`: `karatsubaCost n`
- `runKaratsubaRatio2`: `karatsubaCost n`
- `runKaratsubaRatio4`: `karatsubaCost n`
- `runKaratsubaRatio16`: `karatsubaCost n`
- `runKaratsubaRatioUnder2`: `karatsubaCost n`
- `runFullThenLowInt`: `karatsubaCost n`
- `runClippedLowInt`: `karatsubaCost n`
- `runSchoolbookRat`: `n ^ 2`
- `runKaratsubaRat`: `karatsubaCost n`
- `runKaratsubaSquareRat`: `karatsubaCost n`
- `runFullThenLowRat`: `karatsubaCost n`
- `runClippedLowRat`: `karatsubaCost n`
- `runSchoolbookMod`: `n ^ 2`
- `runKaratsubaMod`: `karatsubaCost n`
- `runKaratsubaSquareMod`: `karatsubaCost n`
- `runFullThenLowMod`: `karatsubaCost n`
- `runClippedLowMod`: `karatsubaCost n`
- `runSeriesSchoolbookInt`: `n ^ 2`
- `runSeriesKaratsubaInt`: `karatsubaCost n`
- `runSeriesSchoolbookRat`: `n ^ 2`
- `runSeriesKaratsubaRat`: `karatsubaCost n`

The fixed informational comparator targets are `runFlintOverhead`,
`runLeanInt64`, `runFlintInt64`, `runLeanInt256`, `runFlintInt256`, `runLeanInt1024`,
`runFlintInt1024`, `runLeanMod64`, `runFlintMod64`, `runLeanMod256`,
`runFlintMod256`, `runLeanMod1024`, and `runFlintMod1024`. Every target has
three repeats and an expected result hash. `runFlintOverhead` exercises the
same warmed persistent subprocess and JSON framing without constructing a
polynomial, so it is the adjustment baseline for both FLINT multiplication
families.

### Newton division

- `runLongDivision`: `n ^ 2`
- `runNewtonDivision`: `karatsubaCost n`
- `runCachedDivision`: `karatsubaCost n`
- `runRepeatedNewtonDivision`: `8 * karatsubaCost n`
- `runRepeatedCachedDivision`: `8 * karatsubaCost n`
- `runSkewLongDivision`: `n ^ 2`
- `runSkewNewtonDivision`: `karatsubaCost n`

### Half-gcd

- `runEuclideanXgcd`: `n ^ 2`
- `runHalfGcd`: `karatsubaCost n * (Nat.log2 n + 1)`
- `runHalfGcdSkew`: `karatsubaCost n * (Nat.log2 n + 1)`
- `runHalfGcdLeft`: `karatsubaCost n * (Nat.log2 n + 1)`

### Multipoint

- `runProductTree`: `karatsubaCost n`
- `runRemainderTree`: `karatsubaCost n`
- `runDirectEval`: `n ^ 2`
- `runMultipointEval`: `karatsubaCost n`
- `runColdMultipointEval`: `karatsubaCost n`
- `runRepeatedDirectEval`: `8 * n ^ 2`
- `runRepeatedMultipointEval`: `8 * karatsubaCost n`
- `runDirectInterpolation`: `n ^ 3`
- `runPlannedInterpolation`: `karatsubaCost n`
- `runColdInterpolation`: `karatsubaCost n`

The tree formulas are the tight models for this Karatsuba implementation:
the per-level costs form a geometric sum. They satisfy the SPEC's more general
`O(M(n) log n)` upper bounds.

### Pade

- `runLinearPade`: `n ^ 3`
- `runHalfGcdPade`: `karatsubaCost n * (Nat.log2 n + 1)`

The `coefficient-kernels` family is owned jointly by the forced Kronecker
targets in `hexpolyz_bench`, the direct and CRT-NTT targets in
`hexpolyfp_bench`, and the transform and balanced CRT targets in
`hexmodarith_bench` and `hexmodular_bench`. Their registrations remain in the
libraries that own the coefficient representation.

## Verdicts

`lake exe hexpolyfast_bench list` and `verify` passed all 57 registrations at
commit `0aaa2af1f`. The two later regression targets
`runKaratsubaRatioUnder2` and `runRemainderTree` passed focused verification at
commit `6bf47916d`. The current registry has 51 parametric and 13 fixed targets
(64 total); the raw schoolbook and blocked-multiplication comparator pairs and
the newly wired `runFlintOverhead` passed focused verification.
The fixed FLINT refresh below also passed every expected hash. A first complete
diagnostic run is retained as
`reports/bench-results/hex-poly-fast-scientific-6f0bbb5a-chungus2-cpu6.json`.
It gave 24 consistent and 23 inconclusive verdicts. That run exposed two
benchmark-design errors: `runProductTree` omitted its `M(n)` factor, and the
exact `Int`/`Rat` division and tree fixtures increasingly measured
coefficient-width growth. Those registrations now use the fixed-width field
above. The clean replacement is
`reports/bench-results/hex-poly-fast-scientific-53ef234e-chungus2-cpu2.json`.
It contains all 47 parametric targets, no killed or budget-truncated row, and
47 `consistent_with_declared_complexity` verdicts:

| target | verdict | β |
|:---|:---:|---:|
| `runSchoolbook` | consistent | -0.017329 |
| `runKaratsuba` | consistent | +0.011398 |
| `runKaratsubaSquare` | consistent | +0.022580 |
| `runKaratsubaSkew` | consistent | -0.053507 |
| `runKaratsubaRatio2` | consistent | +0.037412 |
| `runKaratsubaRatio4` | consistent | -0.005961 |
| `runKaratsubaRatio16` | consistent | -0.043984 |
| `runKaratsubaRatioUnder2` | consistent | -0.022320 |
| `runFullThenLowInt` | consistent | +0.012376 |
| `runClippedLowInt` | consistent | +0.107390 |
| `runSchoolbookRat` | consistent | +0.001593 |
| `runKaratsubaRat` | consistent | +0.012665 |
| `runKaratsubaSquareRat` | consistent | +0.010736 |
| `runFullThenLowRat` | consistent | +0.012852 |
| `runClippedLowRat` | consistent | +0.116438 |
| `runSchoolbookMod` | consistent | -0.011972 |
| `runKaratsubaMod` | consistent | +0.039913 |
| `runKaratsubaSquareMod` | consistent | +0.036096 |
| `runFullThenLowMod` | consistent | +0.032657 |
| `runClippedLowMod` | consistent | +0.130863 |
| `runSeriesSchoolbookInt` | consistent | -0.039582 |
| `runSeriesKaratsubaInt` | consistent | +0.092690 |
| `runSeriesSchoolbookRat` | consistent | -0.005847 |
| `runSeriesKaratsubaRat` | consistent | +0.106338 |
| `runLongDivision` | consistent | -0.025721 |
| `runNewtonDivision` | consistent | +0.025307 |
| `runCachedDivision` | consistent | +0.031378 |
| `runRepeatedNewtonDivision` | consistent | +0.074911 |
| `runRepeatedCachedDivision` | consistent | +0.019557 |
| `runSkewLongDivision` | consistent | -0.048722 |
| `runSkewNewtonDivision` | consistent | -0.021356 |
| `runEuclideanXgcd` | consistent | -0.105758 |
| `runHalfGcd` | consistent | -0.084180 |
| `runHalfGcdSkew` | consistent | +0.004696 |
| `runHalfGcdLeft` | consistent | -0.077145 |
| `runProductTree` | consistent | +0.041852 |
| `runRemainderTree` | consistent | -0.034770 |
| `runDirectEval` | consistent | +0.019097 |
| `runMultipointEval` | consistent | -0.015919 |
| `runColdMultipointEval` | consistent | -0.033578 |
| `runRepeatedDirectEval` | consistent | +0.019778 |
| `runRepeatedMultipointEval` | consistent | -0.004901 |
| `runDirectInterpolation` | consistent | -0.081887 |
| `runPlannedInterpolation` | consistent | +0.016068 |
| `runColdInterpolation` | consistent | -0.011533 |
| `runLinearPade` | consistent | -0.033612 |
| `runHalfGcdPade` | consistent | -0.071212 |

The following within-Lean crossover cells are retained and traceable to the
commits that introduced them. All commands use cold cache mode, three outer
trials, deterministic fixtures, and `--signal-floor-multiplier 1`. The
division, multipoint, interpolation, and Padé commands describe the historical
exact-arithmetic registrations and must be run from their named commits; the
current registrations use `ZMod64 65537` for scientific scaling.

### Bounded series multiplication

Commit `d4d8941a16` recorded:

| coefficients | type | schoolbook | planned Karatsuba |
|---:|:---|---:|---:|
| 4096 | `Int` | 102.388 ms | 1.040 s |
| 4096 | `Rat` | 1.810 s | 1.884 s |
| 8192 | `Rat` | 7.266 s | 6.961 s |

The rational path reaches parity near 8192, but the trial spread is comparable
to the observed win; integer Karatsuba loses decisively. No implicit series
route changed.

```sh
lake exe hexpolyfast_bench compare Hex.PolyFastBench.runSeriesSchoolbookRat Hex.PolyFastBench.runSeriesKaratsubaRat --param-floor 8192 --param-ceiling 8192 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1 --max-seconds-per-call 15
```

### Cached Newton division

Commit `026e27842e` recorded rational division of a `2n + 1` coefficient
dividend by an `n + 1` coefficient divisor:

| `n` | long division | cached Newton |
|---:|---:|---:|
| 256 | 36.891 ms | 42.504 ms |
| 512 | 177.681 ms | 163.155 ms |
| 1024 | 881.427 ms | 648.437 ms |
| 2048 | 5.158 s | 2.875 s |

The cached path crosses between 256 and 512. For eight dividends sharing a
divisor, cached medians at `n = 128, 256, 512` were 98.102 ms, 335.285 ms,
and 1.303 s, against 290.340 ms, 954.347 ms, and 3.451 s when rebuilding the
reciprocal for every dividend.

```sh
lake exe hexpolyfast_bench compare Hex.PolyFastBench.runLongDivision Hex.PolyFastBench.runCachedDivision --param-floor 256 --param-ceiling 1024 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1
```

### Multipoint and interpolation

Commit `2440c312e6` recorded integer evaluation at `n` points:

| `n` | direct Horner | reused plan | cold plan |
|---:|---:|---:|---:|
| 256 | 7.378 ms | 30.602 ms | 73.527 ms |
| 512 | 35.154 ms | 141.703 ms | 316.823 ms |
| 1024 | 196.186 ms | 970.018 ms | 1.777 s |

The product/remainder tree loses on this integer family, including when a
plan is reused for eight polynomials, so no automatic evaluation adoption was
made. The same commit recorded rational interpolation:

| `n` | direct Lagrange | reused plan | cold plan |
|---:|---:|---:|---:|
| 8 | 148.931 us | 35.533 us | 145.636 us |
| 16 | 1.186 ms | 162.831 us | 666.097 us |
| 32 | 12.880 ms | 1.104 ms | 3.381 ms |

The warm plan wins throughout, and the cold plan clearly wins from 16 points.

```sh
lake exe hexpolyfast_bench compare Hex.PolyFastBench.runDirectEval Hex.PolyFastBench.runMultipointEval Hex.PolyFastBench.runColdMultipointEval --param-floor 256 --param-ceiling 1024 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1
lake exe hexpolyfast_bench compare Hex.PolyFastBench.runDirectInterpolation Hex.PolyFastBench.runPlannedInterpolation Hex.PolyFastBench.runColdInterpolation --param-floor 8 --param-ceiling 32 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1
```

### Padé

Commit `3e9d2271bc` recorded exact agreement between the normalized Hankel
linear-system reference and half-gcd Padé on every shared rung through 128:

| `n` | linear algebra | half-gcd |
|---:|---:|---:|
| 32 | 7.908 ms | 20.954 ms |
| 64 | 83.094 ms | 109.469 ms |
| 128 | 981.178 ms | 571.852 ms |

The half-gcd path crosses between 64 and 128.

```sh
lake exe hexpolyfast_bench compare Hex.PolyFastBench.runLinearPade Hex.PolyFastBench.runHalfGcdPade --param-floor 32 --param-ceiling 128 --param-schedule doubling --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1 --max-seconds-per-call 15
```

### Downstream adoption

Commits `17cc8c6a14`, `317cf86294`, `f4a7f70c3`, and `8cd6b25fbe` record the
consumer audit. One-shot finite-field Newton division and half-gcd lost at
every degree from 8 through 2048, so the Fp, GFq, Berlekamp, and
Berlekamp-Zassenhaus consumers retained Euclidean division and gcd.

Multiplication did produce winning cells. `FpPoly.mulFast` selects schoolbook
below 16 coefficients and the packed kernel above it; modular power switches
its compiled loop at modulus size 18. Representative retained/selected
medians were 3.368/1.964 ms for degree-64 modular power, 247.598/188.076 ms
for degree-192 composition, 9.359/6.688 ms for degree-128 GFq power, and
7.452/2.823 ms for the degree-32 Berlekamp Rabin test. Result hashes agreed.

The shared polynomial-product dispatcher admits a balanced tree only in its
measured Hensel domain: 8 through 1023 factors, each with at most two
coefficients and maximum absolute coefficient four. BZ-shaped trial and
reassembly products retain the ordered fold.

## Comparator ratios

The declared informational comparator is FLINT fmpz_poly and nmod_poly via python-flint.
The fixed targets use the persistent oracle process, runtime `IO.Ref` operands,
one discarded warmup iteration, and expected hashes. They
were refreshed at clean binary revision `7dac5bd67` on logical CPU 1 of
`chungus2`. The retained export is
`reports/bench-results/hex-poly-fast-flint-7dac5bd6-chungus2-cpu1.json`.
The exact command was:

```sh
uv run --with python-flint taskset -c 1 .lake/build/bin/hexpolyfast_bench run Hex.PolyFastBench.runFlintOverhead Hex.PolyFastBench.runLeanInt64 Hex.PolyFastBench.runFlintInt64 Hex.PolyFastBench.runLeanInt256 Hex.PolyFastBench.runFlintInt256 Hex.PolyFastBench.runLeanInt1024 Hex.PolyFastBench.runFlintInt1024 Hex.PolyFastBench.runLeanMod64 Hex.PolyFastBench.runFlintMod64 Hex.PolyFastBench.runLeanMod256 Hex.PolyFastBench.runFlintMod256 Hex.PolyFastBench.runLeanMod1024 Hex.PolyFastBench.runFlintMod1024 --export-file reports/bench-results/hex-poly-fast-flint-7dac5bd6-chungus2-cpu1.json
```

The warmed persistent-process and JSON-framing overhead is **6.225 us** per
request. Ratios are `FLINT median / Lean median`; adjusted ratios subtract
6.225 us from the FLINT median before dividing. All six rungs are eligible:
the overhead is below 50% of FLINT wall time and every call is below the 1 s
soft ceiling. The overhead exceeds 5% at both degree-64 rungs, so raw and
adjusted values are reported throughout the ladder for consistency.

| family | `n` | Lean | FLINT | overhead | raw ratio | adjusted ratio | eligible | pair hash |
|---|---:|---:|---:|---:|---:|---:|:---:|:---:|
| `fmpz_poly.mul` | 64 | 49.150 us | 43.629 us | 14.27% | 0.888 | 0.761 | yes | equal |
| `fmpz_poly.mul` | 256 | 466.393 us | 153.187 us | 4.06% | 0.328 | 0.315 | yes | equal |
| `fmpz_poly.mul` | 1024 | 4.642 ms | 621.463 us | 1.00% | 0.134 | 0.133 | yes | equal |
| `nmod_poly.mul` | 64 | 56.444 us | 42.350 us | 14.70% | 0.750 | 0.640 | yes | equal |
| `nmod_poly.mul` | 256 | 571.288 us | 144.441 us | 4.31% | 0.253 | 0.242 | yes | equal |
| `nmod_poly.mul` | 1024 | 5.310 ms | 556.923 us | 1.12% | 0.105 | 0.104 | yes | equal |

Both adjusted curves increasingly favor FLINT: `fmpz_poly` falls from 0.761
to 0.133, and `nmod_poly` from 0.640 to 0.104. This is the trend predicted by
the manifest's informational rationale: FLINT has coefficient-specific
dispatch and tuned native kernels, while these Lean rows deliberately exercise
the generic Karatsuba plan. It does not select a production cell and is not an
unexpected adverse trend.

## Profile

One representative compiled case for every declared input family was sampled
from clean binary revision
`d620e128e6d140a89118856eb9bcc9a5bad7a337` on `chungus2` (AMD EPYC 9455
48-Core Processor, x86-64, NixOS 26.11, Linux 6.12.100). The toolchain was
Lean 4.34.0-rc2, lean-bench 0.1.0 at
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`, samply 0.13.1 at 999 Hz, and
lean-bench-samply at `9356baa2f5757ee40320a897bd284914d5bb9f5e`.
Inputs are deterministic benchmark fixtures and use no random seed.

The exact command form was:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/BENCH_EXE \
  BENCH_NAME PARAM 5000000000
```

The six substitutions, developer-local filtered artefacts, hashes, and filter
diagnostics are below. Raw profiles and symbol sidecars are not committed, as
required by `SPEC/profiling.md`.

| family / executable / target / parameter | filtered profile | SHA-256 | residual | timed | retained / rejected | off-thread | sensitivity |
|---|---|---|---:|---:|---:|---:|---|
| `full-and-clipped-multiplication` / `hexpolyfast_bench` / `runKaratsubaMod`, `n=1024` | `/tmp/hex-profile-runKaratsubaMod-1024.json.gz` | `b25cfe9d8f3736e0c7dc17da72fd0ad9e7abfbd7a832c4b5c162f7c5ae0fb207` | 1.164 ms | 2,782.7 ms | 2,770 / 8 | 0 | passed |
| `newton-division` / `hexpolyfast_bench` / `runRepeatedCachedDivision`, `n=1024` | `/tmp/hex-profile-runRepeatedCachedDivision-1024.json.gz` | `4a039b37969580c96865a7cfd7580c58239091ef5ecdbcf4a301db5803c381e3` | 0.740 ms | 5,541.3 ms | 5,536 / 52 | 0 | passed |
| `half-gcd` / `hexpolyfast_bench` / `runHalfGcd`, `n=2048` | `/tmp/hex-profile-runHalfGcd-2048.json.gz` | `f468d9b27a7c43e587af44371584f74c7fd0fe9e8895a01da71a376e645f2ec3` | 0.511 ms | 4,017.9 ms | 3,997 / 7 | 0 | passed |
| `multipoint` / `hexpolyfast_bench` / `runRepeatedMultipointEval`, `n=2048` | `/tmp/hex-profile-runRepeatedMultipointEval-2048.json.gz` | `e98681adbe1155e262c3f2bcbe3843bf69d96f1b1a7e086b1f047d3f5b328eb5` | 0.589 ms | 4,260.2 ms | 4,256 / 78 | 0 | passed |
| `pade` / `hexpolyfast_bench` / `runHalfGcdPade`, `n=1024` | `/tmp/hex-profile-runHalfGcdPade-1024.json.gz` | `710e4d414af9ccdd632d37e75c0a5b4ad80627b9bd3ab1be511b5e73800f37b6` | 0.550 ms | 5,071.7 ms | 5,051 / 7 | 0 | passed |
| `coefficient-kernels` / `hexpolyfp_bench` / `runMulCrtNttChecksum`, `n=16384` | `/tmp/hex-profile-runMulCrtNttChecksum-16384.json.gz` | `dde646a088116e0c58f4a0b1114077435d05d7a3722da4f174b6c288bb9e19ca` | 0.915 ms | 4,450.3 ms | 4,430 / 15 | 0 | passed |

The first case is the exact `nmod_poly` rung with the worst measured FLINT
gap. The last case covers the downstream coefficient-owner route required by
the SPEC: auxiliary-prime transforms followed by balanced CRT reconstruction.

Leaf self-time, classified from samply's presymbolication sidecars with
`scripts/profile/factor_sampling_profile.py` (SHA-256
`95e4a9642473fe82ca8349724f924d991866f2db40d88921da61f1d98626a6fd`),
was:

| family | own code | GMP | allocation/free | Lean runtime | other | classified |
|---|---:|---:|---:|---:|---:|---:|
| full-and-clipped multiplication | 14.98% | 0.00% | 29.13% | 55.85% | 0.04% | 99.96% |
| Newton division | 15.61% | 0.00% | 31.95% | 52.42% | 0.02% | 99.98% |
| half-gcd | 7.43% | 0.03% | 22.77% | 69.68% | 0.10% | 99.90% |
| multipoint | 13.56% | 0.00% | 34.63% | 51.69% | 0.12% | 99.88% |
| Padé | 16.69% | 0.02% | 37.22% | 46.03% | 0.04% | 99.96% |
| coefficient kernels | 25.28% | 11.26% | 27.36% | 29.14% | 6.95% | 93.05% |

The dominant inclusive Hex costs map directly to registered targets:

- Full multiplication: `runKaratsubaMod` covered 100.00%,
  `mulKaratsubaBalanced` and `karatsubaPlan` 99.71%, `Raw.mulAux` 99.13%,
  and the cutoff leaves in `Raw.schoolbook` 73.50%.
- Newton division: `runRepeatedCachedDivision` covered 100.00%,
  `DivPlan.divMod` 99.89%, `karatsubaPlan` 98.09%, and the quotient's full
  and clipped Karatsuba products about half the profile each.
- Half-gcd: `runHalfGcd` and `xgcdWith` covered 99.72%, `karatsubaPlan`
  97.30%, `Raw.mulAux` 64.72%, and `GcdStep.applyWith` 61.35%.
- Multipoint: `runRepeatedMultipointEval` and `EvalPlan.evalImpl` covered
  99.95%, `DivPlan.divMod` 99.53%, and `karatsubaPlan` 94.08%.
- Padé: `padeBoundary` covered 97.21%; `runHalfGcdPade`, `pade?`, and
  `padeHomogeneous` each covered 97.13%; `reduceToMatrixResult` covered
  97.11% and `karatsubaPlan` 94.61%.
- Coefficient kernels: `FpPoly.mulNttCrt?` covered 76.73%, the registered
  `runMulCrtNttChecksum` wrapper 75.44%, auxiliary-prime convolution and
  image construction 62.55%, forward transforms 26.66%, plan construction
  22.35%, and balanced vector CRT reconstruction 12.60%.

The profiles have the predicted shapes. Fixed-width generic algorithms spend
most leaf samples in Lean runtime and allocation beneath their registered
Karatsuba/division/tree paths. The coefficient-specific route instead exposes
the expected transform, GMP lift, allocation, and CRT costs. No dominant
inclusive cost lies outside a registered benchmark target.

## Concerns

None.
