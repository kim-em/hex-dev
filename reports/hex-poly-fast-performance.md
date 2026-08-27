# HexPolyFast Performance Report

This report is the current audit snapshot for the active, unreleased
`HexPolyFast` library. The implementation is recorded at `done_through: 2`;
this document does not claim a Phase-4 exit.

The retained scientific comparisons were measured on 2026-08-27 on
`chungus2` (AMD EPYC 9455, Linux x86-64) with Lean `4.34.0-rc2`. Each table
below names the commit that introduced the measurement and gives the exact
command needed to refresh it. Inputs are deterministic and have no random
seed. The current smoke and FLINT fixed-target refresh used binary revision
`0aaa2af-dirty`; the only worktree change at that refresh was the
content-preserving relocation of the library SPEC.

## Bench targets

The compiled driver is `bench/HexPolyFast/Bench.lean`, built as
`hexpolyfast_bench`. These are the declared models copied from its
registrations.

### Full-and-clipped multiplication

- `runSchoolbook`: `n ^ 2`
- `runKaratsuba`: `n * Nat.sqrt n`
- `runKaratsubaSquare`: `n * Nat.sqrt n`
- `runKaratsubaSkew`: `n * Nat.sqrt n`
- `runKaratsubaRatio2`: `n * Nat.sqrt n`
- `runKaratsubaRatio4`: `n * Nat.sqrt n`
- `runKaratsubaRatio16`: `n * Nat.sqrt n`
- `runKaratsubaRatioUnder2`: `n * Nat.sqrt n`
- `runFullThenLowInt`: `n * Nat.sqrt n`
- `runClippedLowInt`: `n * Nat.sqrt n`
- `runSchoolbookRat`: `n ^ 2`
- `runKaratsubaRat`: `n * Nat.sqrt n`
- `runKaratsubaSquareRat`: `n * Nat.sqrt n`
- `runFullThenLowRat`: `n * Nat.sqrt n`
- `runClippedLowRat`: `n * Nat.sqrt n`
- `runSchoolbookMod`: `n ^ 2`
- `runKaratsubaMod`: `n * Nat.sqrt n`
- `runKaratsubaSquareMod`: `n * Nat.sqrt n`
- `runFullThenLowMod`: `n * Nat.sqrt n`
- `runClippedLowMod`: `n * Nat.sqrt n`
- `runSeriesSchoolbookInt`: `n ^ 2`
- `runSeriesKaratsubaInt`: `n * Nat.sqrt n`
- `runSeriesSchoolbookRat`: `n ^ 2`
- `runSeriesKaratsubaRat`: `n * Nat.sqrt n`

The fixed informational comparator targets are `runLeanInt64`,
`runFlintInt64`, `runLeanInt256`, `runFlintInt256`, `runLeanInt1024`,
`runFlintInt1024`, `runLeanMod64`, `runFlintMod64`, `runLeanMod256`,
`runFlintMod256`, `runLeanMod1024`, and `runFlintMod1024`. Every target has
three repeats and an expected result hash.

### Newton division

- `runLongDivision`: `n ^ 2`
- `runNewtonDivision`: `n * Nat.sqrt n`
- `runCachedDivision`: `n * Nat.sqrt n`
- `runRepeatedNewtonDivision`: `8 * n * Nat.sqrt n`
- `runRepeatedCachedDivision`: `8 * n * Nat.sqrt n`
- `runSkewLongDivision`: `n ^ 2`
- `runSkewNewtonDivision`: `n * Nat.sqrt n`

### Half-gcd

- `runEuclideanXgcd`: `n ^ 2`
- `runHalfGcd`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runHalfGcdSkew`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runHalfGcdLeft`: `n * Nat.sqrt n * (Nat.log2 n + 1)`

### Multipoint

- `runProductTree`: `n * (Nat.log2 n + 1)`
- `runRemainderTree`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runDirectEval`: `n ^ 2`
- `runMultipointEval`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runColdMultipointEval`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runRepeatedDirectEval`: `8 * n ^ 2`
- `runRepeatedMultipointEval`:
  `8 * n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runDirectInterpolation`: `n ^ 3`
- `runPlannedInterpolation`: `n * Nat.sqrt n * (Nat.log2 n + 1)`
- `runColdInterpolation`: `n * Nat.sqrt n * (Nat.log2 n + 1)`

### Pade

- `runLinearPade`: `n ^ 3`
- `runHalfGcdPade`: `n * Nat.sqrt n * (Nat.log2 n + 1)`

The `coefficient-kernels` family is owned jointly by the forced Kronecker
targets in `hexpolyz_bench`, the direct and CRT-NTT targets in
`hexpolyfp_bench`, and the transform and balanced CRT targets in
`hexmodarith_bench` and `hexmodular_bench`. Their registrations remain in the
libraries that own the coefficient representation.

## Verdicts

`lake exe hexpolyfast_bench list` and `verify` passed all 57 registrations at
commit `0aaa2af1f`. The two later regression targets
`runKaratsubaRatioUnder2` and `runRemainderTree` passed focused verification at
commit `6bf47916d`. The fixed FLINT refresh below also passed every expected
hash. The complete scientific slope export for all 47 parametric targets was
not retained, so no blanket complexity verdict is claimed here.

The following within-Lean crossover cells are retained and traceable to the
commits that introduced them. All commands use cold cache mode, three outer
trials, deterministic fixtures, and `--signal-floor-multiplier 1`.

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

The declared informational comparator is **FLINT fmpz_poly and nmod_poly via
python-flint**. The fixed targets use the persistent oracle process, runtime
`IO.Ref` operands, one discarded warmup iteration, and expected hashes. They
were refreshed at binary revision `0aaa2af-dirty` on `chungus2` with:

```sh
uv run --with python-flint lake exe hexpolyfast_bench compare Hex.PolyFastBench.runLeanInt64 Hex.PolyFastBench.runFlintInt64 Hex.PolyFastBench.runLeanInt256 Hex.PolyFastBench.runFlintInt256 Hex.PolyFastBench.runLeanInt1024 Hex.PolyFastBench.runFlintInt1024 Hex.PolyFastBench.runLeanMod64 Hex.PolyFastBench.runFlintMod64 Hex.PolyFastBench.runLeanMod256 Hex.PolyFastBench.runFlintMod256 Hex.PolyFastBench.runLeanMod1024 Hex.PolyFastBench.runFlintMod1024 --cache-mode cold --outer-trials 3 --signal-floor-multiplier 1
```

Ratios are `FLINT median / Lean median`; values below one favor FLINT.

| family | `n` | Lean | FLINT | ratio | pair hash |
|---|---:|---:|---:|---:|:---|
| `fmpz_poly.mul` | 64 | 32.016 us | 44.365 us | 1.386 | equal |
| `fmpz_poly.mul` | 256 | 317.716 us | 155.525 us | 0.490 | equal |
| `fmpz_poly.mul` | 1024 | 3.074 ms | 617.461 us | 0.201 | equal |
| `nmod_poly.mul` | 64 | 47.231 us | 43.622 us | 0.924 | equal |
| `nmod_poly.mul` | 256 | 509.698 us | 145.518 us | 0.286 | equal |
| `nmod_poly.mul` | 1024 | 4.853 ms | 553.399 us | 0.114 | equal |

Both curves increasingly favor FLINT as degree grows. That trend is expected:
FLINT has coefficient-specific dispatch and tuned native kernels, while these
fixed Lean rows deliberately exercise the generic Karatsuba plan. The
comparison is informational and does not select a production cell.

No separate persistent-transport no-op row was retained. Consequently these
microsecond cells are useful orientation and agreement evidence, but they do
not yet satisfy the report policy's adjusted-overhead calculation.

## Profile

No accepted timed-region sampling profiles have been retained for the six
declared input families:

- `full-and-clipped-multiplication`
- `newton-division`
- `half-gcd`
- `multipoint`
- `pade`
- `coefficient-kernels`

The current host has `samply 0.13.1`, but the required
`lean-bench-samply/scripts/profile_bench.py` orchestration checkout is absent.
The commands should be run only after that tool is installed, because an
unfiltered whole-process profile does not satisfy the timed-region contract.

## Concerns

- The full scientific slope export and per-registration verdicts for all 45
  parametric targets have not been retained.
- The six required timed-region sampling profiles are missing.
- The informational FLINT fixed ladder lacks the separate persistent-process
  overhead measurement needed for adjusted ratios at microsecond rungs.

These are evidence gaps, not known implementation failures. They keep the
library below Phase 4 and must be resolved before `done_through` advances to
4; until then this report is a precise handoff rather than a completion claim.
