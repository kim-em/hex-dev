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
`024645b02a46c0e8125f70c16f4dea0b59a4b9a2`, Lean 4.34.0-rc2,
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
[queries/replay](bench-results/hex-rational-fn-scaling-024645b0-chungus2-cpu3.json),
[normalization/arithmetic](bench-results/hex-rational-fn-families-024645b0-chungus2-cpu1.json),
[remaining axes](bench-results/hex-rational-fn-workloads-024645b0-chungus2-cpu2.json).
β is the fitted slope of time divided by the declared model, not the raw
time exponent.

| Case | Model / mode | β | Signal-eligible rows | Largest-rung median (µs) |
| --- | --- | ---: | ---: | ---: |
| `F.accept` | `n` / 1 | -0.017 | 24/24 | 5534.350 |
| `F.addCancel` | `n` / 1 | -0.018 | 24/24 | 49077.426 |
| `F.addCoprime` | `n` / 1 | -0.005 | 24/24 | 19173.279 |
| `F.addEqual` | `n` / 1 | +0.002 | 24/24 | 19934.795 |
| `F.addShared` | `n` / 1 | -0.005 | 24/24 | 54159.285 |
| `F.addTotal` | `n` / 1 | -0.011 | 24/24 | 345.355 |
| `F.cancelMultiply` | `n` / 1 | -0.009 | 24/24 | 15770.094 |
| `F.checkedDivide` | `n` / 1 | -0.011 | 24/24 | 30203.691 |
| `F.checkedFraction` | `n` / 1 | -0.005 | 24/24 | 15744.032 |
| `F.checkedInverse` | `n` / 1 | -0.001 | 24/24 | 1535.224 |
| `F.divide` | `n` / 1 | -0.012 | 24/24 | 20224.891 |
| `F.generate` | `n` / 1 | +0.011 | 24/24 | 26452.411 |
| `F.inverse` | `n` / 1 | -0.006 | 24/24 | 1547.024 |
| `F.multiply` | `n` / 1 | -0.007 | 24/24 | 28763.304 |
| `F.normalizeCancel` | `n` / 1 | -0.017 | 24/24 | 19305.476 |
| `F.normalizeDegree` | `n` / 1 | -0.010 | 24/24 | 15341.862 |
| `F.subtract` | `n` / 1 | -0.008 | 24/24 | 19179.739 |
| `S.different` | `n` / 1 | +0.072 | 24/24 | 146.458 |
| `S.equal` | `n` / 1 | -0.003 | 24/24 | 232.552 |
| `S.evaluate` | `n` / 1 | +0.010 | 24/24 | 10024.252 |
| `S.evaluatePole` | `n` / 1 | -0.001 | 24/24 | 3146.468 |
| `S.inverse` | `n` / 1 | -0.008 | 24/24 | 111.408 |
| `S.negate` | `n` / 1 | -0.097 | 24/24 | 1197.519 |
| `S.reject` | `n` / 1 | -0.008 | 24/24 | 21651.190 |
| `S.replay` | `n` / 1 | -0.001 | 24/24 | 15146.174 |
| `W.constructors` | `1` / 1 | -0.065 | 24/24 | 0.615 |
| `W.derivative` | `n` / 1 | -0.007 | 24/24 | 22378.008 |
| `W.derivativeCancel` | `n` / 1 | -0.016 | 24/24 | 21793.676 |
| `W.derivativePolynomial` | `n` / 1 | +0.007 | 24/24 | 11947.622 |
| `W.heightAdd` | `n ^ 2` / 2 | -1.341 | 24/24 | 3349.444 |
| `W.heightDerivative` | `n ^ 2` / 2 | -1.478 | 24/24 | 3007.631 |
| `W.heightMultiply` | `n ^ 2` / 2 | -1.196 | 24/24 | 4162.697 |
| `W.heightNormalize` | `n ^ 2` / 2 | -1.259 | 24/24 | 2101.742 |
| `W.multiply` | `M(n)` / 1 | -0.041 | 24/24 | 646785.725 |
| `W.normalizeChain` | `M(n)(log₂n+1)` / 2 | -0.054 | 24/24 | 1135888.367 |
| `W.polynomialPart` | `n` / 1 | +0.002 | 24/24 | 2292.260 |
| `W.power` | `M(n)` / 1 | +0.013 | 24/24 | 29266.112 |
| `W.square` | `M(n)` / 1 | +0.024 | 24/24 | 604500.191 |
| `W.unbalanced` | `n` / 1 | -0.009 | 24/24 | 424156.581 |
| `W.unbalancedSchoolbook` | `n` / 1 | -0.003 | 24/24 | 582010.613 |

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
the growing suffix. Its semantic equality is proved for every fuel, and the
new ratio sweep above passes for both odd and even short lengths. The
unbalanced profile confirms that balanced block products, not output copying,
dominate.

### Fresh-module proof results

The [complete proof export](bench-results/hex-rational-fn-kernel-replay-024645b0-chungus2-cpu22.json)
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
2.76% frequency spread, eight rejected pair attempts, and no exhausted pair.
The effective interference ceiling includes the protocol's three-tick
accounting allowance; the largest accepted effective ratio is 4.48%, not a
claim that every short arm achieved the nominal 0.2% ratio.

The null controls' signed deltas in milliseconds, in recorded round order, are:

- Import: 8.071, 2.369, 8.560, −8.618, 0.154, 3.404; median 2.886,
  IQR 6.197, range 17.178, IQR/build magnitude 0.90%.
- Replay: 6.228, −3.299, −9.458, −4.811, 1.610, 4.855; median −0.845,
  IQR 8.477, range 15.685, IQR/build magnitude 1.07%.

They describe paired noise; the preregistered absolute-only verdict uses
each candidate's maximum raw build time, not a baseline-subtracted estimate.

| Probe | Reference median ms | Candidate median ms | Candidate maximum ms | Budget ms | Candidate .olean bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Replay4 | 687.472 | 791.688 | 802.198 | 5000 | 7432 |
| Replay16 | 686.942 | 791.513 | 846.379 | 5000 | 7440 |
| Replay64 | 688.170 | 779.977 | 791.679 | 5000 | 7440 |
| Reject64 | 682.702 | 783.686 | 795.303 | 5000 | 13352 |

The import-only .olean is 1640 bytes. All certificate theorems report exactly
`[propext, Classical.choice, Quot.sound]`; there is no `sorryAx`,
`native_decide`, added axiom, or trusted external checker. These times are
not added to compiled timings and make no witness-size asymptotic claim.

## Comparator ratios

### Internal alternatives

The [comparison export](bench-results/hex-rational-fn-comparisons-024645b0.json)
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
| 16 | 52.188 | 48.815 | 1.07× |
| 32 | 201.979 | 161.494 | 1.25× |
| 64 | 839.967 | 518.848 | 1.62× |
| 128 | 3151.243 | 1624.486 | 1.94× |

The corresponding names are `runSchoolbookN` and `runKaratsubaAtN`.
On the aggregate four-pair input, cutoffs 1, 2, 4, 8, 16, 32, 64 take
3769.030, 2924.033, 2454.562, 2328.019, 2481.936, 2876.129, 3559.050 µs,
respectively, against schoolbook's 4164.076 µs. Cutoff eight has the smallest
observed aggregate time and remains the default; this is not a claim that
one cutoff is optimal for every field or size.

| Cancellation input degree | Cross-cancel µs | Multiply/normalize µs | Naive/cancel |
| --- | ---: | ---: | ---: |
| 1 | 9.086 | 7.726 | 0.85× |
| 2 | 11.834 | 12.607 | 1.07× |
| 4 | 17.182 | 24.895 | 1.45× |
| 8 | 27.601 | 63.525 | 2.30× |
| 16 | 49.459 | 163.990 | 3.32× |

These are `runCancelN` and `runNaiveN`. The operands are inverse fractions:
cross-cancellation leaves degree-zero products, whereas the naive intermediate
numerator/denominator have degree 2n. The combined `runMultiplication` anchor,
which also includes a non-cancelling product, takes 721.903 µs versus
1501.938 µs for `runMultiplyNormalize`. Cancellation is not promised to win
on the smallest input.

### External rational arithmetic

**FLINT fmpz_poly_q via a persistent C driver** is informational, with no
relative-performance gating goal. The [C driver](../scripts/bench/rationalfn_flint.c)
uses FLINT 3.6.0; the [coordinator](../scripts/bench/rationalfn_flint.py) compares
full canonical `Rat` coefficient arrays after exact representation conversion.
The [54 query cases](bench-results/hex-rational-fn-flint-queries-024645b0-chungus2-cpu5.json)
and [216 arithmetic cases](bench-results/hex-rational-fn-flint-workloads-024645b0-chungus2-cpu5.json)
all agree, including their 30 trivial-input controls. Each export records three
raw trials, source/driver/fixture hashes, affinity, and both representation sizes.

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
| `S.equal` | 29.18 | 4.7/5.1 | 4.8 | 4.9 | 4.8 | 5.0 | 5.0 | 4.9 | 5.0 |
| `S.different` | 25.90 | 35.1/10733.5* | 70.1/5857.4* | 138.8/22495.0* | 364.4/22371.5* | 785.0/—* | 1557.4/—* | 3208.4/—* | 5781.1/—* |
| `S.inverse` | 32.04 | 2.7/3.0 | 2.7 | 2.8 | 2.8 | 2.9 | 2.9 | 2.9 | 2.9 |
| `S.negate` | 31.24 | 39.2/43.1 | 40.7 | 40.0 | 36.7 | 28.5 | 30.4 | 31.3 | 31.6 |
| `S.evaluate` | 40.85 | 73.7 | 70.2 | 76.1 | 72.6 | 74.9 | 74.3 | 77.9 | 79.8 |
| `S.evaluatePole` | 32.56 | 46.7/49.7 | 47.9 | 49.4 | 49.5 | 51.6 | 50.8 | 51.1 | 50.8 |
#### Rational arithmetic: degree axis
| Case | Control (ns) | 32 | 64 | 128 | 256 | 512 | 1024 | 2048 | 4096 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `F.normalizeDegree` | 250.67 | 32.9/35.1 | 65.8/70.4 | 45.3 | 54.0 | 82.4 | 82.4 | 71.6 | 62.7 |
| `F.checkedFraction` | 241.04 | 59.9/67.2 | 64.6/68.9 | 42.7 | 78.5 | 55.7 | 71.1 | 69.6 | 46.6 |
| `F.normalizeCancel` | 241.97 | 102.3/119.3 | 100.7/108.7 | 122.1 | 134.3 | 139.1 | 132.4 | 120.7 | 112.3 |
| `F.addCoprime` | 84.51 | 348.6/424.0 | 337.5/371.3 | 399.8/423.7 | 261.3 | 409.8 | 361.5 | 373.7 | 342.1 |
| `F.addShared` | 338.40 | 202.7/238.4 | 232.8/256.3 | 236.2 | 202.4 | 229.6 | 294.8 | 196.6 | 207.8 |
| `F.addCancel` | 512.73 | 128.3/151.2 | 105.2/112.6 | 167.1/176.8 | 115.0 | 166.4 | 124.1 | 124.6 | 128.0 |
| `F.addTotal` | 158.70 | 1.7/1.9 | 1.3 | 2.1 | 1.4 | 2.0 | 2.2 | 1.6 | 1.6 |
| `F.addEqual` | 223.17 | 50.5/54.1 | 59.1 | 58.6 | 66.8 | 65.2 | 71.0 | 56.0 | 54.6 |
| `F.subtract` | 88.95 | 339.7/415.9 | 366.2/409.2 | 224.9 | 394.8 | 407.9 | 334.1 | 290.7 | 359.3 |
| `F.multiply` | 82.88 | 454.7/539.4 | 473.7/520.1 | 478.4 | 490.3 | 322.5 | 511.3 | 327.0 | 355.4 |
| `F.cancelMultiply` | 259.22 | 43.0/47.0 | 33.5 | 45.4 | 48.0 | 54.0 | 43.1 | 52.7 | 38.5 |
| `F.divide` | 88.97 | 293.7/345.5 | 354.2/391.1 | 208.1 | 279.7 | 368.5 | 320.7 | 300.2 | 290.2 |
| `F.checkedDivide` | 88.45 | 314.8/351.9 | 532.3/587.7 | 550.1 | 369.2 | 344.6 | 518.0 | 514.5 | 507.4 |
| `F.inverse` | 32.41 | 108.5/149.6 | 134.9/163.2 | 146.0/161.3 | 151.5/159.5 | 153.5 | 146.4 | 113.4 | 98.1 |
| `F.checkedInverse` | 32.27 | 126.9/189.9 | 78.9/88.3 | 142.9/158.0 | 153.7/161.8 | 151.2 | 152.5 | 160.6 | 105.7 |
| `W.derivative` | 172.06 | 350.2/509.7 | 220.5/245.9 | 258.1/275.8 | 322.0 | 248.3 | 256.3 | 305.0 | 283.4 |
| `W.derivativeCancel` | 384.17 | 286.9/677.9* | 238.7/320.3 | 233.1/266.9 | 335.5/368.8 | 308.5 | 241.7 | 245.5 | 258.6 |
| `W.derivativePolynomial` | 43.04 | 1140.5/2440.1* | 834.1/1040.0 | 1387.2/1662.4 | 1590.6/1752.6 | 1239.2 | 1203.4 | 1360.0 | 2028.4 |
| `W.multiply` | 54.45 | 1001.1/1166.3 | 608.5 | 1591.0 | 1522.1 | 1813.4 | 2369.1 | 3535.7 | 4042.2 |
| `W.square` | 50.79 | 1107.9/1403.2 | 648.1 | 1134.5 | 1815.7 | 2978.1 | 3034.6 | 3894.4 | 5013.8 |
#### Rational arithmetic: coefficient-height axis
| Case | Control (ns) | 128 | 256 | 512 | 1024 | 2048 | 4096 | 8192 | 16384 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| `W.heightNormalize` | 687.75 | 38.3/53.9 | 32.9/43.3 | 37.8/49.1 | 41.6/51.6 | 34.9/39.3 | 47.2/51.4 | 72.0/76.4 | 130.7 |
| `W.heightAdd` | 199.23 | 82.4/90.3 | 34.8 | 17.8 | 8.2 | 3.4 | 2.1 | 1.5 | 1.3 |
| `W.heightMultiply` | 435.76 | 38.3/43.7 | 26.8/29.0 | 16.1 | 6.5 | 4.0 | 2.8 | 2.7 | 2.3 |
| `W.heightDerivative` | 676.73 | 86.2/104.3 | 83.9/100.6 | 86.8/101.0 | 67.2/73.6 | 48.3 | 52.8 | 65.8 | 47.7 |

The query ratios are broadly flat past the small-input regime. The unequal
query is deliberately ineligible throughout: FLINT rejects the denominator
shape immediately, while Lean reaches the last compared numerator coefficient.
The large raw ratios there are not algorithm-throughput claims.

Short-factor arithmetic ratios fluctuate with shared-host load and fixed
costs but show no sustained extra power of degree. Total addition cancellation
is close to FLINT; nonmonic inversion and rational gcd/short-product paths have
much larger constants. The balanced product and square gaps grow strongly:
for square, 1815.7× at 256 becomes 5013.8× at 4096. This is expected divergence
between different algorithm classes, not a same-class gating failure.
The generic field plan uses Karatsuba and normalized rational arithmetic;
FLINT 3.6's [multiplication](https://github.com/flintlib/flint/blob/v3.6.0/src/fmpz_poly/mul.c)
and [squaring dispatch](https://github.com/flintlib/flint/blob/v3.6.0/src/fmpz_poly/sqr.c)
select packed-integer Kronecker substitution for these small coefficients and
larger lengths in this non-FFT_SMALL build. Requiring a generic field plan to
match that specialized integer backend is not this library's contract.

On the height axis, addition and multiplication ratios shrink sharply toward
the top (1.3× and 2.3×), while normalization worsens to 130.7× and differentiation
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
The [profile export](bench-results/hex-rational-fn-profiles-024645b0.json)
contains full diagnostic blocks, ranked self/inclusive costs, symbolized
function names, child output, commands, hashes, and raw-profile locations.
It covers every manifest input family, the long-chain mode-2 phase, the repaired
unbalanced path, and the worst measured comparator gap (`W.square`, 4096).

The binary/source and host are the same `024645b0` environment as the scientific
runs. Samply is 0.13.1 at 999 Hz. Filtering uses lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`.
With `LEAN_BENCH_PROFILE_KERNEL=1`, each invocation is bracketed by a
`kernel` region; the complete result stays live until after the end timestamp
and is then hashed. Preparation, warmup, output hashing, and reporting are
excluded from these profiles. Profile-only child rows are rejected by ordinary
timing parsers, so they cannot enter a scientific complexity verdict.

| Family / case (parameter) | Timed ms | Samples | Residual ms | Own / GMP / allocation / runtime % | Classified % |
| --- | ---: | ---: | ---: | --- | ---: |
| normalization: `F.normalizeDegree` (4096) | 3893.0 | 3868 | 2.382 | 3.26 / 34.41 / 40.10 / 21.90 | 99.66 |
| addition: `F.addCancel` (4096) | 4049.2 | 2599 | 1.021 | 2.58 / 32.17 / 41.98 / 23.16 | 99.88 |
| multiplication: `W.multiply` (1024) | 3124.3 | 3103 | 0.999 | 2.19 / 31.49 / 43.89 / 22.43 | 100.00 |
| coefficient-height: `W.heightDerivative` (16384) | 5259.2 | 5226 | 2.440 | 0.06 / 81.86 / 17.05 / 1.01 | 99.98 |
| queries: `S.evaluatePole` (65536) | 3094.1 | 3077 | 1.300 | 0.00 / 32.17 / 46.08 / 20.25 | 98.51 |
| calculus: `W.derivativeCancel` (4096) | 2769.1 | 2767 | 0.994 | 1.73 / 39.90 / 35.67 / 21.32 | 98.63 |
| certificate-replay: `F.accept` (65536) | 3829.0 | 1887 | 0.989 | 0.32 / 35.72 / 38.37 / 25.54 | 99.95 |
| normalization: `W.normalizeChain` (2048) | 6799.0 | 6787 | 0.920 | 32.44 / 0.00 / 25.20 / 42.36 | 100.00 |
| multiplication: `W.unbalanced` (512) | 10874.2 | 10822 | 0.990 | 3.38 / 39.82 / 30.25 / 24.97 | 98.42 |
| addition: `F.addCoprime` (4096) | 4778.7 | 4765 | 1.535 | 1.95 / 33.54 / 40.67 / 22.39 | 98.55 |
| calculus: `W.square` (4096) | 10014.7 | 9964 | 0.994 | 2.96 / 35.66 / 34.05 / 27.32 | 99.99 |

Every sensitivity check passes at ±5 ms; each nominal residual is below the
configured five-millisecond threshold. The full diagnostic records also show
expected/retained samples and rejected samples. Low-confidence supplemental
chain captures were discarded; only the successful 2048 case above qualifies.

Inclusive attribution (percentages overlap along call stacks):

- Normalization: `normalizeWith` 100%, `xgcdWith` 64.97%. The constant-length
  Euclidean chain, exact division and coefficient rescaling account for the
  linear family. GMP coefficient arithmetic and allocation dominate leaf cost.
- Addition with cancellation: `addCoreWith` 100%, `cancelWith` 87.73%,
  `xgcdWith` 70.91%. It computes the denominator gcd and cancels X−1 from the
  second gcd. The coprime control similarly has `cancelWith` 76.18% and
  `xgcdWith` 61.18%; these are the registered addition algorithms, not
  unmeasured setup.
- Balanced multiplication: `mulWith` 100%, `mulKaratsuba` 96.39%.
  For the worst-gap square, `powWith` and `polyPowWith` are 100%,
  `Raw.squareAux` 99.70%, schoolbook leaves 61.95%, and combination 21.13%.
  The large external gap is dominated by per-coefficient rational
  arithmetic/allocation through the generic Karatsuba recurrence.
- Unbalanced multiplication: `Raw.blocksInto` 84.39%, `Raw.mulAux` 79.09%,
  schoolbook leaves 55.16%. The tail-recursive accumulator hands a uniquely
  owned array to `Array.set!`; generated C does not increment its array
  reference before the update. Work is concentrated in balanced block products.
- Coefficient-height: GMP occupies 81.86% of leaf samples; normalization is
  64.39% inclusive and xgcd 60.20%. Large integer gcd/multiplication/division,
  rather than polynomial-degree growth, justify the coefficient upper bound.
- Queries: `eval?` is 100% inclusive, traversing the dense pole denominator.
  The bounded-partial-sum Horner loop accounts for the registered linear work.
- Calculus: quotient-rule differentiation spends 75.86% inclusive in
  normalization and 62.70% in xgcd, cancelling the known common X factor.
  The power/square capture separately attributes its balanced recurrence.
- Certificate-replay: `check` and `ofCert?` are each 100% inclusive.
  The two long-witness/linear-polynomial products and the final equality,
  not certificate generation or output hashing, dominate this accepted case.
- Long-chain normalization: `normalizeWith` 99.99%, `xgcdWith` 99.94%.
  Half-gcd matrix products over F₇ account for the published O(M(n) log n)
  phase. GMP is absent, separating this degree experiment from height costs.

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

The first seven captures used a five-second target and affinity
`4-21,23-47,52-69,71-95`; the four supplemental captures used ten seconds and
unrestricted affinity. The target includes calibration probes and is not a
promise of exactly that much retained time. Raw compressed profiles,
presymbolication sidecars and diagnostics are also archived locally under
`.lake/profiles/rational-fn-024645b0/`; analytical summaries and raw hashes are
committed. No large sampled stack dump is required in the source tree.

### Proof-track replacement

Sampling does not measure the advertised kernel-checking surface. Its
replacement is the fresh-module export and trust/provenance record in
§Verdicts; compiled `check` and kernel reduction are never conflated.

## Concerns
