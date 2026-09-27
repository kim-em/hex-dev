# Infinitesimal rational-function performance

The six Mathlib-free targets exercise the production sign and comparison
functions on canonical rational functions. These measurements cover the
infinitesimal implementation only. The libraries remain at phase 0 until the
full real-extension API and its other phase requirements are complete.

## Runtime measurements

Each target uses parameters 128 through 16384, doubling at each rung, with
three trials in fixed trial-major order. Input construction and hashing of the
prepared input are outside the timed loop. Each iteration includes the function
call and consumption of its integer result through hashing and `blackBox`;
the constant-time cases include that harness overhead. The final configuration targets one-second
batches. All six complexity verdicts are consistent with the declared model.
The slope below is the fitted log-log slope of time divided by that model;
zero is the expected value.

| Target | Declared model | Median at 128 | Median at 16384 | Normalized slope |
| --- | --- | ---: | ---: | ---: |
| `second` | n | 12.497 µs | 1550.524 µs | -0.007 |
| `third` | n | 41.783 µs | 5147.753 µs | -0.010 |
| `comparison` | n | 114.850 µs | 14119.644 µs | -0.002 |
| `degree` | 1 | 0.044 µs | 0.044 µs | +0.002 |
| `scan` | n | 0.313 µs | 29.994 µs | -0.031 |
| `height` | 1 | 0.050 µs | 0.050 µs | +0.002 |

`scan` traverses a numerator with n leading zero coefficients over ℚ.
`second` and `third` perform the same outer scan with two and three successive
rational-function levels; their nonzero predecessor coefficients have fixed
size. These measure separate depth cases, not a general asymptotic claim in
tower depth. `comparison` compares X^n with −X^n through canonical subtraction
and sign. Constant denominators keep this family's normalization linear.

`degree` has n+1 nonzero coefficients but finds the constant coefficient
immediately. `height` uses a constant rational with an n-bit numerator and
denominator: comparison with zero does not traverse those limbs. Their
constant-time models apply only to sign on these prepared inputs; they make
no claim about the cost of constructing coefficients or general arithmetic.

The initial 100 ms batch run was below the harness's process measurement
resolution for every row, so its verdicts are inconclusive. Every completed
sample from both runs is retained: [100 ms data](data/hex-ordered-fn/100ms/runtime.json),
[one-second data](data/hex-ordered-fn/1s/runtime.json), with logs and host/CPU
context alongside each. Increasing batch duration changed the measurement
configuration; no samples were rejected because of host activity.

The one-second run used clean commit `65a4556b7792bd69c597dadc18805f255cf919c6`,
Lean 4.34.1, lean-bench 0.1.0, and an automatically selected CPU (56) on
`chungus2`, AMD EPYC 9455, Linux 6.12.100. The JSON records the exact commands,
configuration, per-trial samples, hashes and host context. These absolute
times are observations on this host, not portable limits.

Reproduce after building and committing the sources:

```sh
lake build hexorderedfn_bench
python3 scripts/bench/ordered_fn_measure.py --output /tmp/ordered-fn-runtime
```

## Comparison profile

The representative case is `Hex.OrderedFnBench.comparison`, n=16384, on the
same implementation commit. `perf record` samples user cycles at 999 Hz with
DWARF call stacks, on automatically selected CPU 28. The benchmark's `profile`
command records operation-only regions, excluding preparation and result
hashing. Samply imports the capture; the shared normalization and filtering
scripts retain only those regions on the benchmark thread. Tool versions,
commands and source hashes are in [the context](data/hex-ordered-fn/profile-context.json);
the [summary](data/hex-ordered-fn/profile-summary.json) retains diagnostics and
symbolized rankings. Raw profiles remain at `/tmp/issue-10376-profile`.

| Leaf category | Sample share |
| --- | ---: |
| Hex code | 0.76% |
| GMP | 39.62% |
| Allocation/free | 37.54% |
| Lean runtime | 13.83% |
| Other | 8.24% |

91.76% is classified; unresolved leaves account for 0.82%. Inclusive costs
overlap: `Infinitesimal.compare` covers the whole operation, `normalizeWith`
84.20%, `xgcdWith` 68.70%, polynomial multiplication 42.89%, and polynomial
addition 24.23%. The denominator is constant, so this does not involve a
nonconstant gcd, but the general canonical arithmetic still executes its
normalization machinery. GMP and allocation costs occur within that existing
arithmetic path. The comparison target measures this work; sign scanning
alone would not account for it. This profile does not establish a speedup
against an alternative comparison algorithm.

Filtering diagnostics: 257 operation regions, 3671.1 ms total timed duration,
3665 retained samples, 0.998 ms calibration residual, and a passed ±5 ms
sensitivity check. Profile confidence passes.

## Remaining evidence

The caller-supplied real-extension searches still need their own conformance,
separation-precision and successive-approximation measurements. Clean versus
eager normalization comparisons and downstream tower integration remain part
of the full issue, as do comparison families with nonconstant denominators
and varying coefficient height. This report does not claim completion of
those obligations.
The companion's mathematical theorems have ordinary-kernel regression tests
and axiom audits; applying them is not a performance benchmark.
