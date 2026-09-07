# HexRationalFn performance

## Bench targets

### Compiled computation

The [SPEC's operation-to-track table](../HexRationalFn/SPEC/hex-rational-fn.md#performance-evidence-tracks)
assigns every advertised operation. The Mathlib-free executable
`hexrationalfn_bench` contains 40 scientific registrations and 35 fixed
full-result hash/comparator anchors. Fixed anchors do not satisfy asymptotic
operation coverage and their generic timeouts are not mode-3 claims.

Case prefixes below expand to:

- `S.`: `Hex.RationalFnScaling.`, in [Scaling.lean](../bench/HexRationalFn/Scaling.lean).
- `F.`: `Hex.RationalFnFamilies.`, in [Families.lean](../bench/HexRationalFn/Families.lean).
- `W.`: `Hex.RationalFnWorkloads.`, in [Workloads.lean](../bench/HexRationalFn/Workloads.lean).

All inputs are deterministic; there is no random seed. Preparation is outside
timing. Ordinary scientific calls consume complete output arrays, including
all four generated certificate arrays; equality and replay return Booleans.
Profiles use a separate operation-only boundary, described below.

The seven input families are normalization, addition, multiplication,
coefficient-height, queries, calculus, and certificate-replay. Their independent
axes and strongest applicable complexity modes are:

| Families / cases | Controlled axis and independently derived claim |
| --- | --- |
| Normalization, generation | Mode 1: fixed common linear factor with increasing residual degree, or fixed residual linear factors with increasing common-factor degree. Bounded quotient chains and short exact divisors give Θ(n) coefficient work. |
| Addition, subtraction | Mode 1: coprime, equal, or shared denominators with short cofactors. `addCancel` cancels X−1 in the second gcd; `addTotal` returns zero after scanning opposite dense numerators. All are Θ(n). |
| Unbalanced arithmetic, division | Mode 1: short factors/divisors stay fixed, so the growing coefficient arrays require Θ(n) work. Complete cross-cancellation is paired with an actual growing-output control. |
| Balanced multiplication, square | Mode 1: T(n)=3T(n/2)+Θ(n), hence Θ(n^log₂3), with word-sized coefficients throughout this degree ladder. |
| Long/short multiplication ratio | Mode 1: short lengths m=33 and 64 are fixed, long lengths are mn. n balanced products plus O(mn) accumulation/hash work give Θ(n); schoolbook's Θ(m²n) is also linear on this axis. The odd short length exercises recursive padding. |
| Queries and inversion | Mode 1: independent equal arrays, a mismatch in the last compared coefficient, bounded Horner partial sums, negation, and nonmonic inversion all have Θ(n) work. Monic inversion shares arrays; its Θ(n) result measures full hashing, not an intrinsic linear inversion cost. |
| Calculus and powers | Mode 1: p/X and p/X² give short-divisor linear differentiation, with and without cancellation; polynomial differentiation and splitting have linear scans. Exponent two varies base degree; powers of X+1 over F₇ vary exponent/output degree. The latter's geometrically growing squares sum to O(M(n)), with a largest square of size Θ(n). |
| Constructors and projection | Mode 1: degree stays at most one, and n changes a machine-word coefficient, giving Θ(1) construction/projection and full consumption. |
| Certificate replay | Mode 1: input/output fraction degree stays one; dense Bézout witnesses grow. Two short-factor products, addition, and equality give Θ(n). Acceptance and late rejection are separate cases. |
| Long Euclidean chain | Mode 2: consecutive continuants over F₇ have n linear quotients. The published half-gcd bound is O(M(n) log n). This controlled chain removes rational-height coupling, but cancellations and acceptance of high-half blocks prevent a justified tight wallclock lower bound for this implementation. |
| Coefficient-height | Mode 2: fixed polynomial degrees and O(n)-bit intermediate coefficients give a constant number of field operations, each bounded by O(n²). A tight model is unavailable because GMP chooses data-dependent gcd/division and multiplication paths. |

Here `M(n) = 3^floor(log₂(max(n,1)))`, Θ(n^log₂3) on the power-of-two
ladder. These are family-specific claims, not a generic rational bit-complexity
claim. Degree-family intermediate widths remain machine-word-sized on the
declared schedules. The height families vary rational numerator and denominator
widths separately from degree.

The mode-2 sources are
[van der Hoeven, *Optimizing the half-gcd algorithm*](https://www.texmacs.org/joris/gcd/gcd.pdf)
for O(M(n) log n), and the
[GMP Lehmer-gcd bound](https://gmplib.org/manual/Lehmer_0027s-Algorithm)
together with classical multiplication/division for O(n²). The profile's
long-chain case is dominated by half-gcd/matrix products; the height case is
dominated by GMP arithmetic. Mode 1 was used wherever a controlled family
admits an independent tight derivation; no timing-fitted declaration or
mode-3 compiled escape hatch is used.

### Proof consumer

Literal certificate-check equalities have their own fresh-module track under
[ProofProbe](../bench/HexRationalFn/ProofProbe/Support.lean), built by
`HexRationalFnKernelProbe`. The accepted witnesses have degrees 5, 17, and 65;
the rejected degree-65 certificate changes the final Bézout identity.
The literal payload is a warm import. The measured operation is theorem
elaboration plus kernel checking, not certificate generation or literal
construction.

Each substantive probe has a preregistered five-second **absolute fresh-module**
budget and six rotated, alternating reference/candidate pairs. Import-only and
same-replay null controls are measured first in the declared order. There is
no LeanBench registration, compiled complexity verdict, or sampling-profile
requirement for this proof surface.

`HexRationalFnMathlib` is correspondence-only: its SPEC names
`HexRationalFn` as the computational conformance/performance owner and declares
the `correspondence-only-layer` comparator absence. It owns neither a compiled
benchmark surface nor a proof/tactic performance surface.

## Verdicts

### Compiled scientific results

All 40 registrations pass: 35 mode-1 results are
`consistent_with_declared_complexity`; the four height cases are **within
declared upper bound (observed faster)**, and the long-chain case is **within
declared upper bound (observed matching)**. The height rows' raw harness wording
is `inconclusive` with a negative slope, translated only as the one-sided
mode-2 rule permits.

All measurements below use clean source commit
`83d220225762a783750c110949b37fb80479ba90`, Lean 4.34.0-rc2,
lean-bench commit `8a37daf1074c3bdbd0da479b55538bad4a0022db`,
Linux x86_64 on `chungus2` (AMD EPYC 9455, 48 physical/96 logical CPUs).
This is a shared development host, not a dedicated timing runner. Raw
outer-trial spreads sometimes reach tens of percent; absolute latencies and
small crossover differences should not be interpreted as precise universal
constants.

Scientific settings are unchanged: two-second inner target, three outer
trials, ten-second batch cap, ten-times-startup signal floor, 0.2 leading-rung
warmup exclusion, and slope tolerance 0.15. All 960 measured rows are successful
and signal-eligible. The first rung is then excluded from each fitted slope.
The schedules are:

- `S.*`: 128, 256, 512, 1024, 2048, 4096, 8192, 16384.
- `F.*` and ordinary `W.*`: 32, 64, 128, 256, 512, 1024, 2048, 4096.
- `W.height*`: 128 through 16384 by doubling, in coefficient bits.
- `W.unbalanced*`: 4, 8, 16, 32, 64, 128, 256, 512, in long/short ratio.

```sh
lake build hexrationalfn_bench HexRationalFnKernelProbe
.lake/build/bin/hexrationalfn_bench list
.lake/build/bin/hexrationalfn_bench verify
.lake/build/bin/hexrationalfn_bench sizes
taskset -c 3 .lake/build/bin/hexrationalfn_bench run --filter RationalFnScaling --export-file /tmp/scaling.json
taskset -c 1 .lake/build/bin/hexrationalfn_bench run --filter RationalFnFamilies --export-file /tmp/families.json
taskset -c 2 .lake/build/bin/hexrationalfn_bench run --filter RationalFnWorkloads --export-file /tmp/workloads.json
```

The unmodified exports retain every trial, hash, RSS, startup-floor observation,
configuration, and environment:
[queries/replay](bench-results/hex-rational-fn-scaling-83d22022-chungus2-cpu3.json),
[normalization/arithmetic](bench-results/hex-rational-fn-families-83d22022-chungus2-cpu1.json),
[remaining axes](bench-results/hex-rational-fn-workloads-83d22022-chungus2-cpu2.json).
β is the fitted slope of time divided by the declared model, not the raw
time exponent.

| Case | Model / mode | β | Signal-eligible rows | Largest-rung median (µs) |
| --- | --- | ---: | ---: | ---: |
| `F.accept` | `n` / 1 | -0.014 | 24/24 | 3751.734 |
| `F.addCancel` | `n` / 1 | -0.080 | 24/24 | 32329.279 |
| `F.addCoprime` | `n` / 1 | -0.009 | 24/24 | 19247.119 |
| `F.addEqual` | `n` / 1 | -0.006 | 24/24 | 13330.746 |
| `F.addShared` | `n` / 1 | -0.002 | 24/24 | 56389.649 |
| `F.addTotal` | `n` / 1 | -0.013 | 24/24 | 344.926 |
| `F.cancelMultiply` | `n` / 1 | -0.008 | 24/24 | 10420.919 |
| `F.checkedDivide` | `n` / 1 | -0.011 | 24/24 | 20642.495 |
| `F.checkedFraction` | `n` / 1 | -0.013 | 24/24 | 15785.099 |
| `F.checkedInverse` | `n` / 1 | -0.000 | 24/24 | 1088.900 |
| `F.divide` | `n` / 1 | -0.006 | 24/24 | 20824.098 |
| `F.generate` | `n` / 1 | -0.013 | 24/24 | 24693.746 |
| `F.inverse` | `n` / 1 | -0.003 | 24/24 | 1075.351 |
| `F.multiply` | `n` / 1 | -0.009 | 24/24 | 19309.717 |
| `F.normalizeCancel` | `n` / 1 | -0.009 | 24/24 | 20519.945 |
| `F.normalizeDegree` | `n` / 1 | +0.002 | 24/24 | 23922.930 |
| `F.subtract` | `n` / 1 | -0.009 | 24/24 | 19319.609 |
| `S.different` | `n` / 1 | -0.012 | 24/24 | 111.994 |
| `S.equal` | `n` / 1 | -0.011 | 24/24 | 224.405 |
| `S.evaluate` | `n` / 1 | -0.004 | 24/24 | 9681.097 |
| `S.evaluatePole` | `n` / 1 | -0.002 | 24/24 | 3351.166 |
| `S.inverse` | `n` / 1 | -0.011 | 24/24 | 148.818 |
| `S.negate` | `n` / 1 | +0.003 | 24/24 | 1245.354 |
| `S.reject` | `n` / 1 | -0.023 | 24/24 | 19430.162 |
| `S.replay` | `n` / 1 | -0.002 | 24/24 | 15009.221 |
| `W.constructors` | `1` / 1 | +0.002 | 24/24 | 0.603 |
| `W.derivative` | `n` / 1 | -0.005 | 24/24 | 15152.056 |
| `W.derivativeCancel` | `n` / 1 | -0.014 | 24/24 | 21747.197 |
| `W.derivativePolynomial` | `n` / 1 | -0.002 | 24/24 | 12196.232 |
| `W.heightAdd` | `n ^ 2` / 2 | -1.290 | 24/24 | 2820.852 |
| `W.heightDerivative` | `n ^ 2` / 2 | -1.496 | 24/24 | 2941.033 |
| `W.heightMultiply` | `n ^ 2` / 2 | -1.194 | 24/24 | 4155.314 |
| `W.heightNormalize` | `n ^ 2` / 2 | -1.260 | 24/24 | 2085.730 |
| `W.multiply` | `multiplicationCost n` / 1 | -0.051 | 24/24 | 427563.928 |
| `W.normalizeChain` | `multiplicationCost n * (Nat.log2 n + 1)` / 2 | -0.064 | 24/24 | 1174581.088 |
| `W.polynomialPart` | `n` / 1 | +0.002 | 24/24 | 2432.267 |
| `W.power` | `multiplicationCost n` / 1 | +0.008 | 24/24 | 18925.575 |
| `W.square` | `multiplicationCost n` / 1 | +0.006 | 24/24 | 405943.876 |
| `W.unbalanced` | `n` / 1 | -0.017 | 24/24 | 646721.504 |
| `W.unbalancedSchoolbook` | `n` / 1 | +0.001 | 24/24 | 592990.147 |

The 35 fixed anchors also pass their frozen expected hashes. They provide
conformance and common-domain comparisons, not operation-coverage evidence.
`sizes` validates the equality mismatch location, full polynomial plan
agreement, certificate acceptance/rejection, and raw/canonical sizes.

Regression evidence is retained, not reclassified as passing:
the [791f17ca family export](bench-results/hex-rational-fn-families-791f17ca-chungus2-cpu13.json)
exposes near-quadratic short-operand multiplication/division.
The corrected [4918f828 export](bench-results/hex-rational-fn-families-4918f828-chungus2-cpu15.json)
passes the 15 original linear families. Short operands now use schoolbook
multiplication and short divisors/quotients use direct division. General
unbalanced blocking additionally uses a unique accumulator instead of copying
the growing suffix. For input lengths L and S, its preallocated capacity is
L + 2 max(min(blockSize,L),S) + 1;
coefficient updates use a list-free tail-recursive loop, and empty terminal
tails allocate nothing. Its semantic equality is proved for every fuel, and the
new ratio sweep above passes for both odd and even short lengths. The
unbalanced profile confirms that balanced block products, not output copying,
dominate.

### Fresh-module proof results

The [complete proof export](bench-results/hex-rational-fn-kernel-replay-83d22022-chungus2-cpu22.json)
has `measurement_state: complete`, `release_quality: true`, and no validity
exceptions. It records the full local import closure's SHA-256 hashes,
toolchain/dependency checkout identities, cache/import boundary, compiler
artifacts, axiom sets, raw rotated samples, resource counters, and every
rejected attempt/preflight window.

```sh
python3 scripts/bench/rationalfn_kernel_replay.py \
  --shared-host --expected-host chungus2 --cpu 22 --samples 6 \
  --max-pair-retries 32 --output /tmp/kernel-replay.json
```

Each timed arm is `lake build +MODULE:olean` after its own outputs are removed;
`lake build +MODULE:deps` warms only imports. CPU 22 and SMT sibling 70 are
checked together. The accepted run contains 72 arm-frequency observations,
2.69% frequency spread, one rejected pair attempt, and no exhausted pair.
The effective interference ceiling includes the protocol's three-tick
accounting allowance; the largest accepted effective ratio is 4.46%, not a
claim that every short arm achieved the nominal 0.2% ratio.

The null controls' signed deltas in milliseconds, in recorded round order, are:

- Import: 6.852, -31.584, -30.132, -0.797, -3.809, 159.286; median -2.303,
  IQR 28.491, range 190.870, IQR/build magnitude 4.02%.
- Replay: 4.333, -5.845, 57.912, -9.863, 6.022, -55.723; median -0.756,
  IQR 14.458, range 113.635, IQR/build magnitude 1.82%.

They describe paired noise; the preregistered absolute-only verdict uses
each candidate's maximum raw build time, not a baseline-subtracted estimate.

| Probe | Reference median ms | Candidate median ms | Candidate maximum ms | Budget ms | Candidate .olean bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Replay4 | 689.535 | 779.114 | 1075.234 | 5000 | 7432 |
| Replay16 | 726.329 | 802.122 | 1010.709 | 5000 | 7440 |
| Replay64 | 692.759 | 793.046 | 1012.960 | 5000 | 7440 |
| Reject64 | 694.578 | 803.541 | 874.809 | 5000 | 13352 |

The import-only .olean is 1640 bytes. All certificate theorems report exactly
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`,
`native_decide`, added axiom, or trusted external checker. These times are
not added to compiled timings and make no witness-size asymptotic claim.

## Comparator ratios

### Internal alternatives

The [comparison export](bench-results/hex-rational-fn-comparisons-83d22022.json)
retains all native results and exact commands. Every group reports
`allAgreed` on its intentional common domain: eight schoolbook/Karatsuba
plans on the same four polynomial pairs; four individual product-size
crossovers; cancelled versus multiply-then-normalize at five common sizes;
the combined multiplication anchor; and both unbalanced algorithms at all
eight ratio rungs. Output hashes consume the complete canonical result.

All commands have the form
`taskset -c 4 .lake/build/bin/hexrationalfn_bench compare NAME1 NAME2 ... --export-file FILE`.
Fixed names use prefix `Hex.RationalFnBench.`.

| Product coefficient count | Schoolbook µs | Default Karatsuba µs | Schoolbook/default |
| --- | ---: | ---: | ---: |
| 16 | 55.041 | 51.779 | 1.06× |
| 32 | 213.232 | 168.207 | 1.27× |
| 64 | 844.500 | 541.101 | 1.56× |
| 128 | 3394.647 | 1707.558 | 1.99× |

The corresponding names are `runSchoolbookN` and `runKaratsubaAtN`.
On the aggregate four-pair input, cutoffs 1, 2, 4, 8, 16, 32, 64 take
4017.693, 3211.442, 2686.531, 2518.147, 2672.731, 3156.093, 3777.805 µs,
respectively, against schoolbook's 4568.232 µs. Cutoff 8 has the smallest
observed aggregate time. The default remains eight; small crossover differences
on this shared host do not establish an optimal cutoff for every field or size.

| Cancellation input degree | Cross-cancel µs | Multiply/normalize µs | Naive/cancel |
| --- | ---: | ---: | ---: |
| 1 | 9.984 | 8.362 | 0.84× |
| 2 | 13.179 | 14.051 | 1.07× |
| 4 | 18.961 | 26.049 | 1.37× |
| 8 | 29.335 | 66.296 | 2.26× |
| 16 | 50.563 | 175.492 | 3.47× |

These are `runCancelN` and `runNaiveN`. The operands are inverse fractions:
cross-cancellation leaves degree-zero products, whereas the naive intermediate
numerator/denominator have degree 2n. The combined `runMultiplication` anchor,
which also includes a non-cancelling product, takes 762.650 µs versus
1600.578 µs for `runMultiplyNormalize`. Cancellation is not promised to win
on the smallest input.

### External rational arithmetic

**FLINT fmpz_poly_q via a persistent C driver** is informational, with no
relative-performance gating goal. The [C driver](../scripts/bench/rationalfn_flint.c)
uses FLINT 3.6.0; the [coordinator](../scripts/bench/rationalfn_flint.py) compares
full canonical `Rat` coefficient arrays after exact representation conversion.
The [54 query cases](bench-results/hex-rational-fn-flint-queries-83d22022-chungus2-cpu5.json)
and [216 arithmetic cases](bench-results/hex-rational-fn-flint-workloads-83d22022-chungus2-cpu5.json)
all agree, including their 30 trivial-input controls. Each export records three
raw trials, source/driver/fixture hashes, affinity, and both representation sizes.
The coordinator records its own checkout, including a dirty flag that counts
untracked files. All cited exports have `git_dirty: false`; write measurement
outputs outside the checkout (as below) until the run is complete. Informational
FLINT timings do not themselves issue a release-quality verdict.

FLINT stores an integer-polynomial pair with scalar normalization; Hex stores
rational coefficients with monic denominator. Parsing, input conversion,
input canonicalization for ordinary arithmetic, output conversion, and comparison
are outside C timing. Normalization copies the raw input outside each timed
canonicalization. Process I/O is outside both timers. Native full-output hashing
is inside ordinary timing, whereas FLINT output consumption is outside:
the ratios are end-to-end native benchmark / C operation ratios, not
equal-overhead kernel ratios.

Total inverse/division at zero is adapted explicitly to zero without calling
FLINT's rejecting operation; rejected raw denominators are not given a
throughput time. Evaluation poles remain failures. The
[FLINT rational-function interface](https://flintlib.org/doc/fmpz_poly_q.html)
is not a certificate producer/checker: that absence is
`no-comparable-surface-in-named-comparator`. Polynomial-part splitting is
`structural-layer`, owned by HexPolyFast division evidence. Prime-field
operations use internal plan/conformance comparisons.

```sh
cc -O2 -Wall -Wextra scripts/bench/rationalfn_flint.c -lflint -o /tmp/rationalfn-flint
.lake/build/bin/hexrationalfn_bench emit-scaling > /tmp/queries.jsonl
.lake/build/bin/hexrationalfn_bench emit-workloads > /tmp/workloads.jsonl
taskset -c 5 python3 scripts/bench/rationalfn_flint.py /tmp/rationalfn-flint \
  /tmp/queries.jsonl --json --trials 3 --repeats 10000
taskset -c 5 python3 scripts/bench/rationalfn_flint.py /tmp/rationalfn-flint \
  /tmp/workloads.jsonl --json --trials 3 --repeats 100
```

On Nix, compilation additionally uses the FLINT include/lib paths
recorded by the build environment; the linked version has `FFT_SMALL` disabled.

Each table cell is the raw ratio (×). A slash adds the overhead-adjusted ratio
when the zero-parameter control exceeds 5% of C time. Adjustment subtracts
that conservative tiny-input control from C time, not from native time.
An asterisk marks an ineligible C rung (>50% control share); “—” means the
subtraction is nonpositive. Ineligible values are shown only for completeness.
Every C operation remains below the ten-second ceiling; eight shared rungs
per case expose the trend without extending the ladder past a wallclock cap.

#### Queries: degree axis

| Case | Control (ns) | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `S.equal` | 30.63 | 4.4/4.7 | 4.6 | 4.5 | 4.9 | 4.2 | 4.2 | 4.8 | 4.7 |
| `S.different` | 27.04 | 34.2/2598.6* | 67.0/14622.1* | 136.1/—* | 268.7/—* | 544.2/—* | 1075.5/—* | 2079.7/—* | 3941.2/81208.1* |
| `S.inverse` | 33.03 | 3.5/3.8 | 3.7 | 3.7 | 3.8 | 3.8 | 3.7 | 3.7 | 3.7 |
| `S.negate` | 33.37 | 26.1/28.7 | 28.5 | 29.7 | 30.5 | 31.4 | 32.0 | 29.8 | 23.8 |
| `S.evaluate` | 45.74 | 67.2 | 71.3 | 72.2 | 73.0 | 76.1 | 71.0 | 70.0 | 46.9 |
| `S.evaluatePole` | 33.49 | 44.8/47.6 | 48.5 | 51.1 | 46.2 | 49.2 | 48.4 | 48.3 | 32.6 |

#### Rational arithmetic: degree axis

| Case | Control (ns) | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `F.normalizeDegree` | 419.72 | 53.8/60.5 | 69.6/75.3 | 67.3 | 74.2 | 83.2 | 86.0 | 101.5 | 101.2 |
| `F.checkedFraction` | 417.52 | 41.5/47.4 | 46.6/50.4 | 48.7 | 74.4 | 55.2 | 55.4 | 58.9 | 54.1 |
| `F.normalizeCancel` | 414.03 | 59.6/69.1 | 74.7/82.3 | 81.6/86.1 | 133.2 | 142.1 | 96.0 | 103.3 | 97.1 |
| `F.addCoprime` | 136.99 | 226.8/278.9 | 228.3/253.4 | 239.3/252.8 | 378.7 | 404.3 | 255.6 | 390.3 | 324.2 |
| `F.addShared` | 590.39 | 129.8/155.0 | 148.5/164.9 | 158.7/168.2 | 273.4 | 260.7 | 278.8 | 203.3 | 221.3 |
| `F.addCancel` | 980.61 | 81.2/100.8 | 90.6/102.4 | 100.0/106.8 | 161.4/170.4 | 107.9 | 117.3 | 134.7 | 98.4 |
| `F.addTotal` | 296.73 | 1.1/1.2 | 1.2/1.3 | 1.3 | 1.3 | 1.5 | 1.5 | 1.6 | 1.6 |
| `F.addEqual` | 432.26 | 22.1/24.1 | 25.2/26.5 | 26.1 | 44.4 | 30.5 | 44.5 | 32.2 | 30.5 |
| `F.subtract` | 154.00 | 227.8/289.3 | 233.5/263.8 | 238.5/253.7 | 374.4 | 259.3 | 326.3 | 273.6 | 385.1 |
| `F.multiply` | 84.84 | 187.5/207.8 | 200.5/211.9 | 200.5 | 203.1 | 221.4 | 338.9 | 230.0 | 224.2 |
| `F.cancelMultiply` | 267.10 | 26.0/28.3 | 19.6 | 21.7 | 30.7 | 25.7 | 25.5 | 25.7 | 29.7 |
| `F.divide` | 144.43 | 202.5/242.4 | 210.7/231.8 | 210.9 | 349.3 | 375.2 | 318.0 | 245.3 | 244.8 |
| `F.checkedDivide` | 147.24 | 203.3/244.6 | 210.6/231.9 | 217.2 | 209.6 | 229.1 | 241.7 | 379.2 | 244.8 |
| `F.inverse` | 40.08 | 59.3/81.2 | 62.7/73.4 | 94.3/106.2 | 100.2/106.5 | 91.8 | 107.3 | 73.5 | 79.8 |
| `F.checkedInverse` | 39.85 | 59.0/80.7 | 59.3/68.9 | 95.0/106.9 | 102.0/108.5 | 99.4 | 72.6 | 71.9 | 74.7 |
| `W.derivative` | 218.63 | 148.2/198.9 | 150.5/173.8 | 204.4/225.5 | 221.8/233.9 | 226.8 | 220.7 | 211.5 | 161.0 |
| `W.derivativeCancel` | 335.90 | 197.1/297.9 | 214.8/267.8 | 227.0/254.7 | 241.0/256.0 | 287.4 | 243.2 | 245.0 | 229.0 |
| `W.derivativePolynomial` | 40.80 | 793.6/1203.7 | 886.2/1092.6 | 970.2/1082.4 | 1031.4/1092.8 | 1102.3 | 1681.2 | 1262.8 | 1277.8 |
| `W.multiply` | 47.52 | 603.7/674.2 | 486.7 | 1011.2 | 1330.0 | 1244.3 | 2068.3 | 2054.3 | 2854.5 |
| `W.square` | 50.87 | 602.0/725.3 | 512.2 | 1214.9 | 1523.6 | 1502.3 | 2367.0 | 2535.1 | 2885.2 |

#### Rational arithmetic: coefficient-height axis

| Case | Control (ns) | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `W.heightNormalize` | 1129.58 | 32.5/53.9 | 31.2/49.8 | 50.7/103.8* | 38.9/56.0 | 37.5/46.8 | 66.5/82.3 | 76.8/85.4 | 101.1/107.0 |
| `W.heightAdd` | 327.24 | 38.0/42.1 | 23.0 | 12.2 | 5.9 | 3.4 | 2.0 | 1.4 | 0.9 |
| `W.heightMultiply` | 419.19 | 36.8/41.5 | 25.3/27.2 | 15.3 | 8.1 | 5.0 | 3.3 | 2.6 | 2.0 |
| `W.heightDerivative` | 778.72 | 87.5/108.3 | 80.0/97.7 | 88.0/104.3 | 81.3/92.1 | 53.3/56.8 | 52.2 | 46.5 | 44.6 |

The query ratios are broadly flat past the small-input regime. The unequal
query is deliberately ineligible throughout: FLINT rejects the denominator
shape immediately, while Lean reaches the last compared numerator coefficient.
The large raw ratios there are not algorithm-throughput claims.

Short-factor arithmetic ratios fluctuate with shared-host load and fixed
costs but show no sustained extra power of degree. Total addition cancellation
is close to FLINT; nonmonic inversion and rational gcd/short-product paths have
much larger constants. The balanced product and square gaps grow strongly:
for square, 1523.6× at 256 becomes 2885.2× at 4096. This is expected divergence
between different algorithm classes, not a same-class gating failure.
The generic field plan uses Karatsuba and normalized rational arithmetic;
FLINT 3.6's [multiplication](https://github.com/flintlib/flint/blob/v3.6.0/src/fmpz_poly/mul.c)
and [squaring dispatch](https://github.com/flintlib/flint/blob/v3.6.0/src/fmpz_poly/sqr.c)
select packed-integer Kronecker substitution for these small coefficients and
larger lengths in this non-FFT_SMALL build. Requiring a generic field plan to
match that specialized integer backend is not this library's contract.

On the height axis, addition and multiplication ratios shrink sharply toward
the top (0.9× and 2.0×), while normalization reaches 101.1× and differentiation
remains tens of times slower. These are fixed-degree, data-dependent
coefficient-arithmetic/representation effects, not evidence for a new fitted
polynomial-degree model. The mode-2 bounds remain one-sided.

Intermediate and final sizes are recorded per fixture, not inferred from a
result hash. Normalization records monic gcd and both cofactors; arithmetic
records uncancelled products; differentiation records quotient-rule numerator,
denominator, and cancelled gcd. For example, at 16384 height bits the derivative
has maximum canonical Hex coefficient widths 32771/5 bits, while FLINT's
integer-pair widths are 32771/32773 bits. Both represent the same rational
function. The intermediate size fields use a minimum width of one bit for a
zero polynomial; final `sizes` fields use zero for empty arrays.

### Proof-track comparator replacement

Kernel replay has no FLINT protocol comparator. Its matched import baseline,
same-module controls, raw build budgets, and artifacts are the separate
comparison evidence in §Verdicts. There is no synthetic ratio combining
kernel-build and compiled-operation times.

## Profile

### Compiled timed regions

All eleven captures below pass calibration, sample-count and sensitivity
checks, and classify at least 98% of retained leaf samples.
The [profile export](bench-results/hex-rational-fn-profiles-83d22022.json)
contains full diagnostic blocks, ranked self/inclusive costs, symbolized
function names, child output, commands, hashes, and raw-profile locations.
It covers every manifest input family, the long-chain mode-2 phase, the repaired
unbalanced path, and the worst eligible raw comparator gap (`W.square`, 4096).

The binary/source and host are the same `83d22022` environment as the scientific
runs. Samply is 0.13.1 at 999 Hz. Filtering uses lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`.
With `LEAN_BENCH_PROFILE_KERNEL=1`, each invocation is bracketed by a
`kernel` region; the complete result stays live until after the end timestamp
and is then hashed. Preparation, warmup, output hashing, and reporting are
excluded from these profiles. Profile-only child rows are rejected by ordinary
timing parsers, so they cannot enter a scientific complexity verdict.

| Family / case (parameter) | Timed ms | Samples | Residual ms | Own / GMP / allocation / runtime % | Classified % |
| --- | ---: | ---: | ---: | --- | ---: |
| normalization: `F.normalizeDegree` (4096) | 8335.6 | 8268 | 3.291 | 3.17 / 32.78 / 42.67 / 21.00 | 99.61 |
| addition: `F.addCancel` (4096) | 6661.3 | 6564 | 2.430 | 2.86 / 46.89 / 25.93 / 23.99 | 99.68 |
| multiplication: `W.multiply` (1024) | 10134.2 | 10054 | 2.432 | 4.26 / 41.93 / 23.92 / 29.86 | 99.97 |
| coefficient-height: `W.heightDerivative` (16384) | 6381.7 | 6334 | 2.637 | 0.13 / 78.86 / 18.69 / 2.19 | 99.87 |
| queries: `S.evaluatePole` (65536) | 9484.6 | 9362 | 4.193 | 0.00 / 38.41 / 35.77 / 25.32 | 99.50 |
| calculus: `W.derivativeCancel` (4096) | 5564.6 | 5545 | 1.000 | 2.00 / 37.31 / 39.91 / 20.67 | 99.89 |
| certificate-replay: `F.accept` (65536) | 7535.6 | 7528 | 0.998 | 0.31 / 36.17 / 37.41 / 26.01 | 99.89 |
| normalization: `W.normalizeChain` (2048) | 7029.6 | 7028 | 0.976 | 32.98 / 0.00 / 23.82 / 43.20 | 100.00 |
| multiplication: `W.unbalanced` (512) | 7031.6 | 7009 | 0.970 | 2.21 / 33.57 / 42.25 / 21.91 | 99.94 |
| addition: `F.addCoprime` (4096) | 9575.9 | 9547 | 0.999 | 2.23 / 36.10 / 37.02 / 23.02 | 98.37 |
| calculus: `W.square` (4096) | 6714.9 | 6697 | 0.898 | 2.20 / 35.69 / 36.51 / 25.61 | 100.00 |

Every sensitivity check passes at ±5 ms; each nominal residual is below the
configured five-millisecond threshold. The full diagnostic records also show
expected/retained samples and rejected samples. Only captures passing every
confidence check are included.

Inclusive attribution (percentages overlap along call stacks; tail calls can
remove the caller's frame):

- `F.normalizeDegree`: `normalizeWith` 100.00%, `xgcdWith` 64.56%.
- `F.addCancel`: `addCoreWith` 100.00%, `cancelWith` 87.66%, `xgcdWith` 71.21%.
- `W.multiply`: `mulWith` 100.00%, `mulKaratsuba` 96.37%.
- `W.heightDerivative`: `normalizeWith` 64.95%, `xgcdWith` 60.99%.
- `S.evaluatePole`: `eval?` 99.94%.
- `W.derivativeCancel`: `RationalFn.derivativeWith` 23.88%, `normalizeWith` 76.09%, `xgcdWith` 62.56%.
- `F.accept`: `ofCert?` 100.00%, `check` 100.00%.
- `W.normalizeChain`: `normalizeWith` 99.99%, `xgcdWith` 99.93%.
- `W.unbalanced`: `blocksInto` 84.81%, `mulAux` 80.87%, `schoolbook` 56.76%.
- `F.addCoprime`: `cancelWith` 76.44%, `xgcdWith` 61.18%.
- `W.square`: `powWith` 100.00%, `polyPowWith` 100.00%, `squareAux` 99.72%, `schoolbook` 62.74%, `combine` 20.83%.

Normalization and addition are dominated by gcd, exact division, coefficient
rescaling, and allocation. The second addition gcd cancels X−1 on `addCancel`; the
coprime control measures the same arithmetic path without that cancellation.
Balanced products and squares follow the generic Karatsuba recurrence with
rational schoolbook leaves. The unbalanced path spends its time in balanced
block products; its list-free accumulator hands a uniquely owned array to
`Array.set!`, and generated C does not increment that array reference before
the update. The coefficient-height case is dominated by GMP arithmetic, while
the F₇ long-chain experiment isolates half-gcd/matrix products without GMP.
Queries traverse the dense pole denominator. Differentiation performs the
quotient rule and cancels the known X factor. Certificate acceptance measures
the two long-witness/linear-polynomial products and final equality, not
certificate generation or output hashing.

All dominant phases therefore map to named registrations and their polynomial
backend; no unexplained dominant cost is assigned to a fixed anchor.

Reproduce a capture with the table's full case name and parameter:

```sh
env LEAN_BENCH_PROFILE_KERNEL=1 \
  python3 /tmp/lean-bench-samply/scripts/profile_bench.py \
  --bench-exe .lake/build/bin/hexrationalfn_bench \
  --bench-name Hex.RationalFnWorkloads.square --param 4096 \
  --target-nanos 10000000000 --label-filter kernel \
  --out /tmp/square-kernel.json.gz \
  --samply-args '--rate 999 --unstable-presymbolicate'
python3 scripts/profile/summarize_profile.py /tmp/square-kernel.json.gz \
  --thread hexrationalfn_bench --top 100 --output /tmp/square-summary.json
```

All captures used a ten-second target and unrestricted affinity. The target
includes calibration probes and is not a
promise of exactly that much retained time. Raw compressed profiles,
presymbolication sidecars and diagnostics are also archived locally under
`.lake/profiles/rational-fn-83d22022/`; analytical summaries and raw hashes are
committed. No large sampled stack dump is required in the source tree.

### Proof-track replacement

Sampling does not measure the advertised kernel-checking surface. Its
replacement is the fresh-module export and trust/provenance record in
§Verdicts; compiled `check` and kernel reduction are never conflated.

## Concerns
