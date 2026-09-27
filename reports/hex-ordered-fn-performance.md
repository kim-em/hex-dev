# Ordered rational-function performance

The Mathlib-free targets exercise production signs, comparisons, Horner bounds
and real refinement on canonical rational functions. The initial six targets
cover infinitesimals; the later sections cover real searches and general comparisons. The APIs are implemented (phase 1); independent review and the remaining
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
symbolized rankings. The raw capture was collected at `/tmp/issue-10376-profile`
and is no longer available; the committed context and summary support the
reported attribution but do not permit re-filtering that capture.

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
initial measurements. The current search configuration uses eight larger
parameters (8192, 12288, 16384, 24576, 32768, 49152, 65536, 98304), with a
60-second configured per-call cap. The driver used one Lean worker, starving
the parent timeout task behind pipe reads; completed calls therefore exceed
that setting. Those samples are retained. The driver now uses four workers,
all pinned to the same selected CPU. A regression check with a 0.25-second cap
kills the n=8192 approximation child with four workers; the same check with
one worker instead completes a 1.854-second operation. The
[cap-check logs](data/hex-ordered-fn/cap-four-workers.log) and
[single-worker reproduction](data/hex-ordered-fn/cap-one-worker.log) are functional
checks of the watchdog, not performance evidence. The configuration
keeps the same quadratic model; the
initial data remain evidence for their recorded smaller schedule. Both schedules
remain unresolved evidence, without a Phase-4 completion claim.

## Corrected comparison and height measurements

The [second configuration](data/hex-ordered-fn/height/runtime.json) corrects the
denominator recurrence and extends the three height ladders to 65,536–8,388,608
bits. These changes were made before collection; no completed samples were
replaced. All four two-sided verdicts now pass. The same fixed trial-major
schedule uses three trials and one-second batches. The [context](data/hex-ordered-fn/height/context.json)
records the automatically selected CPU, source commit and executable hash.
These are separate scaling runs, not paired before/after speedup measurements.

| Target | Model | First median | Last median | Normalized slope |
| --- | --- | ---: | ---: | ---: |
| `denominators` | 3 ^ Nat.log2 (max n 1) | 129.255 µs | 141733.434 µs | -0.105 |
| `compareHeight` | n | 8.571 µs | 953.451 µs | +0.071 |
| `realHeight` | n | 19.123 µs | 2137.468 µs | -0.005 |
| `provider` | n | 23.551 µs | 3434.430 µs | +0.040 |

## Larger search measurements

The [larger search run](data/hex-ordered-fn/search-large/runtime.json) retains
all 96 completed samples: eight parameters from 8192 through 98304, three
trial-major repetitions, and four targets. Every row completed successfully;
all four complexity verdicts are inconclusive in the slower-than-declared
direction. The table reports the first and last median and the fitted slope
of time divided by n². The configured leading warmup trim excludes the first
rung from the fit; its samples and displayed median are still retained.

| Target | Median at 8192 | Median at 98304 | Normalized slope |
| --- | ---: | ---: | ---: |
| `refinement` | 324.199 ms | 113.927 s | +0.371 |
| `jointRefinement` | 830.633 ms | 321.040 s | +0.393 |
| `horner` | 97.860 ms | 25.596 s | +0.253 |
| `approximation` | 1632.345 ms | 628.837 s | +0.389 |

The [context](data/hex-ordered-fn/search-large/context.json) records automatically
selected CPU 36, host load, command and binary hash. The executable was built
from clean source commit `71590d87470f3770fdf52e4cb757d07499a502b3` and was
unchanged throughout collection. The checkout advanced during the run; the
approximation family's per-child metadata therefore records the later checkout
commit `538e9c511b64db7aef401594ceeef5b975a7d47e`, not a different executable.
The run used one Lean worker, including the timeout limitation described above.
No completed samples were discarded or replaced because of host activity.

These results reject the provisional quadratic scaling claim over this range.
They establish neither a replacement two-sided model nor a passing upper-bound
claim. Together with the profile below, they identify the omitted cost of
large-rational arithmetic for further characterization.

## Search work counts

These exact counts follow the executed loops for the benchmark families. A
coefficient visit is one coefficient-provider call. Each Horner coefficient
performs one bound multiplication and one bound addition. A bound multiplication
uses four rational products and min/max selection; a bound addition uses two
rational additions. Constant-provider calls occur once per polynomial enclosure.
Failed numerator separation skips the denominator enclosure in `Real.attempt`.
Approximation trials enclose both polynomials and try four-corner bound division.

| Family | Last trial index | Coefficient visits | Constant-provider calls | Bound operations |
| --- | ---: | ---: | ---: | ---: |
| `refinement` | n | 2n+3 | n+2 | 4n+6 |
| `jointRefinement` | n+1 | 2n+5 | n+3 | 4n+10 |
| `horner` | 0 | n+2 | 2 | 2n+4 |
| `realHeight` (n≥1) | 0 | 3 | 2 | 6 |
| `approximation` | n+3 | 3n+12 | 2n+8 | 7n+28 |

The approximation count includes one bound division per trial; each trial also
computes the quotient width and compares it with the requested width. Formal
zero performs no provider calls. These counts exclude preparation and the
preparation-time witness check.

For exact-coefficient refinement, the numerator enclosure at trial k is
[2⁻ⁿ−2⁻ᵏ⁻¹, 2⁻ⁿ+2⁻ᵏ⁻¹], so the first success is k=n. With joint refinement,
its lower endpoint is 2⁻ⁿ−2δ+δ²/4, with δ=2⁻ᵏ, so the first success is k=n+1.
For approximation, the eventual quotient width is
(5δ+δ³/4)/(1−δ²/4); it first meets 2⁻ⁿ at k=n+3. Exact Fraction evaluation
independently checks these endpoint formulas at n=0,1,4,16,64.

Stored endpoint bit sizes also explain the coupled parameters in the unresolved
runs. Joint refinement's final lower numerator bound is 2⁻²ⁿ⁻⁴, whose denominator
has 2n+5 bits. The Horner numerator bounds are [2⁻ⁿ, 2−2⁻ⁿ], with n+1-bit
numerator/denominator components. `realHeight` produces n+2-bit endpoint
components. The final approximation width has a denominator with 3n+10 bits.
These describe reduced rational values, not GMP scratch storage or unreduced
internal multiplication temporaries. The timings include all of that arithmetic.

## Search arithmetic profile

The larger search ladder exceeds the provisional quadratic model. A profile of
`approximation` at n=8192 identifies large-integer arithmetic as the dominant
cost: GMP accounts for 90.69% of leaf samples, allocation/free 8.24%, Lean
runtime 0.61%, Hex code 0.02%, and other code 0.43%. Multiplication routines
feature prominently: `__gmpn_addmul_1_x86_64` alone accounts for 39.85% of leaf
samples. Thus the earlier linear-bit-cost assumption for each rational operation
is inadequate. The exact operation counts remain valid; they do not imply a
quadratic runtime bound when rational multiplication and division are included.
This profile does not establish a replacement asymptotic model.
The GMP manual describes the operand-size-dependent costs of
[Karatsuba multiplication](https://gmplib.org/manual/Karatsuba-Multiplication)
and [subquadratic GCD](https://gmplib.org/manual/Subquadratic-GCD); counting
rational operations alone does not account for those costs.

The [context](data/hex-ordered-fn/search-profile-context.json) records the
capture command, automatically selected CPU and executable hash; the
[summary](data/hex-ordered-fn/search-profile-summary.json) retains symbolized
rankings and filtering diagnostics. The executable is exactly the one used by
the larger search run, built from `71590d87470f3770fdf52e4cb757d07499a502b3`.
The checkout had since advanced to `4229c31ac56f2c782545ff1dd47481fdfd4554fe`;
that later hash in the profile's child metadata is not the executable's source.

User-cycle sampling at 999 Hz with DWARF call stacks retained 4888 samples in
three operation regions totaling 4893.9 ms, including calibration calls but
excluding preparation and hashing. Clock normalization matches every raw perf
timestamp exactly. The wall/monotonic anchor was captured after the run;
region alignment residual is 0.492 ms and the ±5 ms sensitivity check passes.
Leaf attribution is the basis for the percentages above. Deep GMP stacks do
not consistently unwind to the caller, so incomplete inclusive caller shares
are not used to divide costs between Horner evaluation and quotient enclosure.
The raw capture was collected at `/tmp/issue-10376-search-profile` and is
no longer available. The committed summary and context retain attribution and
alignment diagnostics, but cannot substitute for raw data when re-filtering.

## Remaining evidence

Complete search cost characterization and successive approximation measurements
remain outstanding. Clean versus eager normalization
comparisons and downstream tower integration also remain part of the full issue.
The existing [RationalFn arithmetic report](hex-rational-fn-performance.md#internal-alternatives)
provides cancellation versus multiply-then-normalize comparisons on identical
canonical operands, but does not replace the ordered-extension measurements.
The companion's mathematical theorems have ordinary-kernel regression tests
and axiom audits; applying them is not a performance benchmark.
