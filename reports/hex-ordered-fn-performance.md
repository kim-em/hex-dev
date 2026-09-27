# Infinitesimal rational-function performance

The six Mathlib-free targets exercise the production sign and comparison
functions on canonical rational functions. These measurements cover the
infinitesimal implementation only. The APIs are implemented (phase 1); independent review and the remaining
conformance/performance gates are tracked separately.

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

## Real refinement and general comparisons

The Mathlib-free executable also measures the actual `Real.sign` and `Real.approx`
searches. Preparation checks a finite successful trial and constructs the erased
accessibility proof. The timed operation starts at precision zero, so earlier
failed attempts remain included. These rational test subjects do not assert a
universal transcendental registration; the companion Liouville fixture supplies
that separate semantic integration test.

The [initial measurements](data/hex-ordered-fn/real-initial/runtime.json) use three
trial-major repetitions and one-second batches on automatically selected CPU 44.
[Context](data/hex-ordered-fn/real-initial/context.json) records the command, binary
hash and source commit `1c06686b749266a21ea01600b431871e7a93e210`. Module documentation
and phase metadata were edited during collection; the measured executable was
unchanged. Per-child repository metadata is preserved in the raw export.
All completed rows are retained. All eight provisional complexity verdicts
were inconclusive in the faster-than-declared direction, rather than passes.

| Target | Parameters | Initial model | First median | Last median | Normalized slope |
| --- | --- | --- | ---: | ---: | ---: |
| `denominators` | 16–2048 | n * n | 202.695 µs | 226815.890 µs | -0.521 |
| `compareHeight` | 1024–131072 | n | 5.648 µs | 14.521 µs | -0.787 |
| `refinement` | 16–2048 | n * n | 60.742 µs | 24232.628 µs | -0.815 |
| `jointRefinement` | 16–2048 | n * n | 96.580 µs | 46499.510 µs | -0.773 |
| `horner` | 16–2048 | n * n | 21.555 µs | 9035.260 µs | -0.770 |
| `realHeight` | 1024–131072 | n | 5.476 µs | 36.114 µs | -0.562 |
| `approximation` | 16–2048 | n * n | 188.906 µs | 85064.051 µs | -0.769 |
| `provider` | 16–2048 | n | 0.444 µs | 2.109 µs | -0.837 |

`refinement` uses X−(2−2⁻ⁿ) at subject 2. `jointRefinement` also narrows every
coefficient. `approximation` requests width 2⁻ⁿ for X−1 with both coefficient
and argument refinement. Their witness checks are outside the timer; execution
still includes all failed trials. `horner` signs 1+X+⋯+Xⁿ using argument bounds
[−1/2,1/2]. `realHeight` varies the height of a linear polynomial's coefficient.
`provider` isolates the caller's construction of rational bounds. No analytic
constant generator is measured.

The original quadratic denominator model overlooked the default Karatsuba plan;
the corrected recurrence is T(n)=3T(n/2)+Θ(n). The height/provider ladders are
extended to larger operands to distinguish limb work from fixed overhead. The
quadratic bit-work models for refinement and Horner are not established by the
initial measurements. Their results remain unresolved evidence, without a
Phase-4 completion claim.

## Remaining evidence

Complete search cost characterization, operation/bit-size counts and successive
approximation measurements remain outstanding. Clean versus eager normalization
comparisons and downstream tower integration also remain part of the full issue.
The existing [RationalFn arithmetic report](hex-rational-fn-performance.md#internal-alternatives)
provides cancellation versus multiply-then-normalize comparisons on identical
canonical operands, but does not replace the ordered-extension measurements.
The companion's mathematical theorems have ordinary-kernel regression tests
and axiom audits; applying them is not a performance benchmark.
