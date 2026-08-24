# HexBerlekamp Performance Report

Current at revision `f396965d439aeaffcb3f843d85998b23765a22b2`, measured
2026-08-22 on `chungus2` (AMD EPYC 9455, NixOS 26.11, Linux x86-64), timing
runs pinned to CPU 0 (`taskset -c 0`), machine idle-checked before
measurement. LeanBench 0.1.0, Lean 4.33.0-rc1, python-flint 0.9.0 through the
warmed persistent driver.

## Bench Targets

The four parametric registrations in `bench/HexBerlekamp/Bench.lean` use these
declared complexity expressions, copied from their registration sites, one per
declared input family:

- `Hex.BerlekampBench.runBerlekampMatrixChecksum`: `n * n`
  (`berlekamp-matrix` family; iterative Frobenius columns at fixed `p = 5`).
- `Hex.BerlekampBench.runRabinTestChecksum`: `n * n * n`
  (`rabin-irreducibility` family; the dense Frobenius power dominates).
- `Hex.BerlekampBench.runBerlekampFactorChecksum`: `n * n`
  (`split-step-factorization` family; constant-bounded gcd loop over the
  field constants).
- `Hex.BerlekampBench.runDistinctDegreeChecksum`: `n * n * n`
  (`distinct-degree-factorization` family; Frobenius updates against the
  residual dominate).

The Rabin and DDF ladders additionally carry one fixed Lean registration and
one fixed FLINT registration per rung (`runRabinTestChecksumN` /
`runFlintRabinTestChecksumN` at `n = 8..64`, `runDistinctDegreeChecksumN` /
`runFlintDistinctDegreeChecksumN` at `n = 12..96`), sharing inputs prepared
during module initialization outside the measured child region. The FLINT
targets use `flintCompareConfig` (`warmupFirstIter := true`,
`minTotalSeconds := 0.2`), which spawns the persistent driver outside the
timed region and amortises steady-state work, and the paired Lean targets use
the matching `leanCompareConfig` floor. `runBerlekampFullySplitChecksum` is a
fixed regression for the complete recursive splitter. The declared
`phase4.input_families` in `libraries.yml` are the coverage contract for this
report; each family is exercised by exactly one parametric ladder above.

## Verdicts

Scientific run on clean commit `f396965d`, exported to
`reports/bench-results/hex-berlekamp-f396965d-chungus2.json` (SHA-256
`3df932c38c25668158a99725f06db6d19234108936c658577a3271260fe58cb2`).
Command: `taskset -c 0 lake exe hexberlekamp_bench run <four parametric
targets> --export-file ...`. `list` and `verify` pass in CI on every PR.

| Target | Family | Largest rung | Median | β | Verdict |
|---|---|---:|---:|---:|---|
| `runBerlekampMatrixChecksum` | `berlekamp-matrix` | 192 | 12.702 ms | -0.026 | consistent |
| `runRabinTestChecksum` | `rabin-irreducibility` | 64 | 49.422 ms | -0.254 | consistent |
| `runBerlekampFactorChecksum` | `split-step-factorization` | 256 | 3.785 ms | -0.251 | consistent |
| `runDistinctDegreeChecksum` | `distinct-degree-factorization` | 96 | 215.369 ms | -0.345 | consistent |

All four verdicts are `consistent_with_declared_complexity` with the
registered slope tolerance 0.35.

## Comparator Ratios

Both declared comparators are `informational` (see `libraries.yml` and the
SPEC's External comparators section): the measured gap is the structural
constant-factor cost of verified generic `FpPoly` arithmetic against FLINT's
hand-tuned C word-level kernels, recorded for orientation.

**FLINT nmod_poly.is_irreducible via python-flint**, paired against the Lean
`rabin-irreducibility` fixed ladder. Export:
`reports/bench-results/hex-berlekamp-rabin-compare-f396965d-chungus2.json`
(SHA-256
`dcd6a7f255202048fb2225549236d140dafde8cf5f1ef0870e4e356e3759f338`).

| n | Lean median | FLINT median | ratio |
|---:|---:|---:|---:|
| 8 | 0.132 ms | 12.8 µs | 10.3x |
| 16 | 0.806 ms | 18.5 µs | 43.6x |
| 24 | 2.327 ms | 23.8 µs | 97.9x |
| 32 | 5.575 ms | 42.4 µs | 131.4x |
| 48 | 20.293 ms | 68.2 µs | 297.4x |
| 64 | 45.004 ms | 120.6 µs | 373.3x |

**FLINT nmod_poly.factor_distinct_deg via python-flint**, paired against the
Lean `distinct-degree-factorization` fixed ladder. Export:
`reports/bench-results/hex-berlekamp-ddf-compare-f396965d-chungus2.json`
(SHA-256
`32f79d561e1056a26c78c8f822078023180a934e89a54aed1a21179ab27a4deb`).

| n | Lean median | FLINT median | ratio |
|---:|---:|---:|---:|
| 12 | 1.372 ms | 21.5 µs | 63.9x |
| 24 | 4.203 ms | 44.6 µs | 94.2x |
| 32 | 8.948 ms | 45.7 µs | 195.8x |
| 48 | 53.096 ms | 153.2 µs | 346.7x |
| 64 | 61.218 ms | 204.9 µs | 298.7x |
| 96 | 214.028 ms | 285.7 µs | 749.3x |

Command per surface: `taskset -c 0 lake exe hexberlekamp_bench run --filter
{RabinTestChecksum,DistinctDegreeChecksum} --export-file ...`, all repeats
hash-agreeing, driver spawned out of the timed region.

## Profile

Sampling profiles were captured for one representative rung of each input
family with samply 0.13.1 at interval 1.001 ms (~999 Hz) through
`scripts/profile/run_profile.sh` (lean-bench-samply orchestrator, filtered to
the timed regions, target 3 s per capture), binary built from clean
`f396965d`. Leaf-cost categorisation (own code / Lean runtime / allocator) is
committed as
`reports/bench-results/berlekamp-leafcost-f396965d-chungus2.txt` (SHA-256
`2a91ece372fb44d7148d5f64068e64440a3182ebe227f79c9b9bf51332527d72`); the raw
`*.json.gz` profiles are developer-local per SPEC/profiling.md.

| Capture | own code | Lean runtime | allocator | top leaf symbols |
|---|---:|---:|---:|---|
| `berlekamp-matrix`, n=192 (4057 samples) | 33.8% | 37.6% | 27.9% | `lean_apply_2` 15.7%, `DensePoly.mulImpl` 7.2% |
| `rabin-irreducibility`, n=64 (2547 samples) | 33.2% | 37.7% | 28.7% | `lean_apply_2` 19.9%, `DensePoly.mulImpl` 8.8% |
| `split-step-factorization`, n=256 (1926 samples) | 45.5% | 27.3% | 27.1% | `DensePoly.subtractScaledShiftStep` 20.9%, `ZMod64.mul` boxed 10.5% |
| `distinct-degree-factorization`, n=96 (1921 samples) | 35.8% | 34.7% | 29.2% | `lean_apply_2` 18.7%, `mi_free` 17.1% |

The distribution matches what the algorithms should be doing: the three
Frobenius-dominated families spend their own-code time in `DensePoly.mulImpl`
and the monic-reduction kernel, with roughly a quarter to a third of wall
time in boxed closure dispatch (`lean_apply_2`) plus reference counting, and
another ~28% in the allocator (`mi_malloc_small`/`mi_free`), the expected
shape for boxed generic field arithmetic over small `F_5` elements. The
split-step family is the most kernel-bound (45.5% own code, led by the
Euclidean `subtractScaledShiftStep` at 20.9%), matching its gcd-loop cost
model. The same boxed-arithmetic overhead is the structural component of the
FLINT ratios above. No sample category contradicts a declared cost model; no
audit-found issue was filed from these captures.

## Concerns

None.
