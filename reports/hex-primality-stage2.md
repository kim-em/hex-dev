# Pollard p−1 stage-2 arithmetic

The prepared full-scan continuation matches its declared modular-operation
model on all four operand-size tracks, both with batch traces and with counters
only. The eight lean-bench registrations each retain five trials at all five
rungs: 200 completed samples, with no removals or reruns.

Standalone evidence covers the phase decomposition, endpoint and double-bound
factor tracks, full misses, empty/whole/recovery controls, paired trace overhead,
and a full scan at the primitive cap. Both consumer flags remain false:
ordinary factorization reserves one extra continuation attempt without
displacing stage 1 or ECM. Construction has separate native and interpreted
evidence; whole-module diagnostic timing is not a search-performance gate.

## Inputs and arithmetic

The [70 shared fixtures](../conformance-fixtures/HexPrimality/pminusone-stage2.jsonl)
include the SPEC's small and large factor tables, distinct prime cofactors, full
order witnesses for the supplied factors, and recursive Pocklington witnesses
for the cofactors. Preparation rejects a cofactor if its base-2 order can be
captured by any interval prime through `2*q`. The
[fixture verifier](../scripts/bench/pminusone_stage2_fixtures.py) checks these
conditions independently. Generated Lean fixtures also replay every prime
certificate and check the saved stage-1 residues with HexPrimality's checker.

These measurements use the small-factor table, base 2, `B₁ = 64`, and
`B₂ = q-1`. Every nonempty interval is a full miss. Preparation supplies the
saved stage-1 residue and complete prime interval outside the timer. The
continuation constructs all 210 babies, advances the giant, evaluates terms,
accumulates products, and flushes 32-candidate batches. It uses direct `Nat`
multiplication and remainder at every modulus size. Stage 1's word-Montgomery
`powMod` dispatch is outside these measurements.

The first interval prime is 67, so the initial giant exponent and its binary
power cost are both zero. For `L` primes and `G` giant advances, the exact
multiplication count is `210 + G + 2*L`. The benchmark guards verify that count
and the number of batch gcds for every fixture. Prepared execution has no
preflight gcds; the public raw-residue adapter adds two.

| q | L | G | Modular multiplications | Batch gcds |
|---:|---:|---:|---:|---:|
| 2039 | 290 | 9 | 799 | 10 |
| 4093 | 545 | 19 | 1319 | 18 |
| 8191 | 1009 | 38 | 2266 | 32 |
| 16381 | 1881 | 77 | 4049 | 59 |
| 32749 | 3493 | 155 | 7351 | 110 |

The working-residue upper bound is 252, excluding the sieve, prime indices,
and optional trace. Peak process RSS in the raw export includes the Lean
runtime and prepared fixture/certificate data and is not an algorithm-only
storage measurement. Trace checksumming traverses the retained batch records;
its linear cost is included in the trace arm.

## Measurements

The [runner](../scripts/bench/pminusone_stage2_sweep.py) uses lean-bench's fixed
trial-major schedule, pinned to automatically selected CPU 4 on `chungus2`.
Host load was recorded as context and did not reject any sample. Source hashes,
the executable hash, command, affinity, complete raw timings, and harness
environment are retained in the
[measurement artifact](bench-results/pminusone-stage2-scaling.json), with the
[native export](bench-results/pminusone-stage2-scaling.native.json) and
[console log](bench-results/pminusone-stage2-scaling.log).
Compressed JSONL collections preserve every record; their SHA-256 identifiers
refer to the decompressed bytes. The measurement verifiers accept both plain
and gzip-compressed collections.

The table gives median milliseconds at `q = 32749`. Beta is the harness's
slope of normalized cost against the parameter; every verdict is
`consistent_with_declared_complexity` using the declared tolerance 0.5.
These arms were independent scaling runs, so their timing differences are
not a paired estimate of trace overhead.

| Modulus bits | Batch trace (ms) | Counters (ms) | Trace beta | Counters beta |
|---:|---:|---:|---:|---:|
| 64 | 1.433 | 1.450 | +0.040 | +0.043 |
| 128 | 1.464 | 1.479 | +0.030 | +0.032 |
| 256 | 1.644 | 1.633 | +0.035 | +0.031 |
| 512 | 2.361 | 2.360 | +0.047 | +0.046 |

Reproduce the run with a fresh output path to preserve completed samples:

```sh
python3 scripts/bench/pminusone_stage2_fixtures.py
lake build hexprimality_bench
python3 scripts/bench/pminusone_stage2_sweep.py \
  --output reports/bench-results/pminusone-stage2-scaling-new.json
```

## Standalone phases and trace overhead

The [phase collection](bench-results/pminusone-phases-native.jsonl.gz) retains
3,690 samples: five trial-major passes over all 40 small-factor fixtures at
`q-1`, `q`, and `2*q`, plus the three fixed factor/whole/recovery controls.
Every continuation and total result matches its expected outcome. The
[independent measurement checker](../scripts/bench/check_pminusone_measurements.py)
also validates candidate powers, batch products, recovery order, and exact
operation counts across all 2,495 retained continuation/total samples (407
distinct deterministic executions, including the trace and cap collections). Each sample uses the lean-bench fixed child runner, with a 1 ms auto-tuning
floor, preparation outside the native timer, and output serialization outside
it. The raw row records the chosen repeat count, output hash, and peak RSS. The six phases are also fixed registrations in the
existing primality benchmark executable.

Median milliseconds per call on the full miss at `q = 32749`:

| Modulus bits | Setup | Enumeration alone | Stage 1 | Prepared stage 2 | Continuation | Total |
|---:|---:|---:|---:|---:|---:|---:|
| 64 | 1.555 | 1.567 | 0.008 | 1.512 | 3.009 | 3.075 |
| 128 | 1.586 | 1.540 | 0.021 | 1.619 | 3.099 | 3.145 |
| 256 | 1.566 | 1.568 | 0.022 | 1.830 | 3.342 | 3.389 |
| 512 | 1.554 | 1.533 | 0.033 | 2.559 | 4.038 | 4.071 |

Setup measures base normalization, setup gcd, and enumeration for both stages.
The enumeration-only column isolates the continuation's sieve/readback/filter.
Stage 1 measures its existing `powMod` loop and final gcd on prepared primes.
On word moduli that loop constructs a `MontCtx` for each of its 18 powers;
those constructions and conversions remain included in the stage-1 column.
There is no persistent big-integer modular context. With `B₁ = 64`, the binary
power schedules execute 162 multiplications, below the 196-operation upper
bound, excluding word-context conversions. The continuation column includes
raw-residue normalization, both preflight gcds, enumeration, and arithmetic.
Total independently executes stage 1 and continuation exactly once; it is not
a sum of independently timed columns.

The [prepared-context collection](bench-results/pminusone-preparation-native.jsonl.gz)
separates preparation from stage-1 exponentiation and its final gcd. It retains
430 samples: five trial-major passes over the 40 full-miss fixtures and three
fixed controls, on automatically selected CPU 7. Preparation includes base
normalization, base gcd, both prime enumerations, and one word-sized Montgomery
context where the existing dispatch uses that backend. Exponentiation receives
the prepared context, retaining entry/exit conversions for every power. Larger
moduli use the existing direct `Nat` fallback with no context allocation.

| Modulus bits | Preparation (ms) | Prepared stage 1 (ms) |
|---:|---:|---:|
| 64 | 1.789 | 0.003 |
| 128 | 1.807 | 0.022 |
| 256 | 1.781 | 0.025 |
| 512 | 1.756 | 0.035 |

`preparePower_eq` proves that each prepared power equals `HexArith.powMod`;
`preparedSmooth_eq` proves equality of the complete successive-power loop.
All 40 saved residues are checked before timing. The independent oracle also
checks every preparation checksum and final gcd, covering 86 distinct
executions. These are separate phase measurements, so subtracting them from
the preceding table would not isolate context cost. The production stage-1
loop and all consumer comparisons retain their per-power context construction;
their total timings include that cost. Reproduce these boundaries with
`python3 scripts/bench/pminusone_stage2_measure.py preparation --output <fresh-path>`.

The [adjacent trace comparison](bench-results/pminusone-trace-native.jsonl.gz)
retains all 640 samples from eight AB/BA blocks over the 40 full-miss fixtures.
Both modes agree on result, attempts, generator state, and every counter after
removing retained batch detail. The fixed child runner uses a 10 ms auto-tuning
floor. At `q = 32749`, median trace/counter time ratios
are 1.003, 1.016, 1.008, and 0.999 for 64, 128, 256, and 512 bits respectively.
These small differences establish no material trace premium on this host and
family; they do not establish that trace allocation is free on other inputs.
The empty `q = 67` interval is retained solely as an early-return control.

The [shared sieve/readback scaling collection](bench-results/pminusone-enumeration-scaling.json)
retains 30 samples over six nonempty rungs, 1000 through 32000, in five
trial-major passes. Its existing `N * sqrt(N)` model prices operations on the
large packed bitset plus readback. The verdict is
`consistent_with_declared_complexity`, with normalized slope −0.593 and the
registration's tolerance 0.6. This is a conservative cost model, not a claim
that measured wall time has an exact exponent 1.5.

## Primitive cap and storage

The [cap collection](bench-results/pminusone-cap-native.jsonl.gz) runs five passes
at `(B₁,B₂) = (524288,4194304)` with raw residue 2 modulo `2^521-1`. The
base-2 order is 521, which is outside the prime interval. More strongly,
`gcd(2^q-1,2^521-1) = 2^gcd(q,521)-1 = 1` for each interval prime,
so every batch product is a unit and every run is a full miss. This is a raw-residue continuation control, not a stage-1-ready fixture.

There are 252,557 candidates, 17,476 giant advances, 7,893 batch gcds, and
522,816 modular multiplications, including 16 for the initial giant power.
The raw adapter adds two setup gcds and reports one attempt without changing
the generator. Median enumeration, prepared arithmetic, and raw continuation
times are respectively 1.764 s, 0.195 s, and 1.909 s. Each cap sample is a single invocation timed by
the lean-bench fixed child runner. Enumeration dominates
this endpoint, so prepared-only timing would substantially understate total
adapter cost.

The algorithm's live arithmetic storage is bounded by 252 residues. Enumeration
also retains an O(B₂)-bit sieve and up to π(B₂) prime indices. Full batch traces
retain one gcd value per flushed batch plus at most 32 recovery values; these
are additional to the arithmetic bound. The raw artifacts retain all batch
boundaries and executed gcds. Process RSS is not an algorithm-only storage
measurement.

## Representative attribution

The [profile manifest](bench-results/pminusone-profile.json) identifies the
executable, source hashes, automatically selected CPU, host load, and replayable
capture commands. Its [summary](bench-results/pminusone-profile.json.attempt/summary.json)
contains 4,909 samples filtered to the prepared 512-bit full-miss timed region
at `q = 32749`. Timestamp calibration has 0.812 ms trimmed boundary residual;
97.64% of leaf samples are classified and 0.20% are unresolved.

GMP accounts for 63.45% of leaf samples and allocation for 27.11%. Inclusive
stacks place 46.16% in candidate-term computation, 12.02% in batch flushes,
1.41% in baby-table construction, and 1.26% in giant advancement. Division and
remainder, temporary big-integer allocation, and batch gcds therefore explain
the observed cost. The modular-operation model counts their executed calls
at a fixed operand size; it does not treat a 512-bit modular operation as the
same wall-time unit as a word Montgomery multiplication.

## Consumer controls

The [fixed field-prime diagnostic corpus](bench-results/pminusone-stage2-construction-corpus.jsonl.gz)
contains eight adjacent AB/BA blocks with the unchanged construction budget,
including `maxAttempts = 1024` and `maxBits = 512`. Neither arm constructs any
of the four certificates. P-521 is rejected by the bit ceiling in both arms.
These records establish checked outcomes and route behavior; their diagnostic
timers are not used for the native acceptance gate. Native gate timings use
the lean-bench registrations and the
[construction collection](bench-results/pminusone-construction-native.jsonl.gz).
Exhaustion timings are never counted as successful-certificate timings.

The [prime-parent fixtures](../conformance-fixtures/HexPrimality/pminusone-stage2-parents.jsonl)
make each small-factor semiprime `p*r` a predecessor obligation of an exactly
certified prime `N = 2*k*p*r+1`. Their two Pocklington witnesses and the
previously checked child certificates establish primality independently of
search. The native and interpreted construction comparisons use the same
1024-attempt budget in both arms. For these parents only, both arms explicitly
allow 1024 bits so the parent of a 512-bit predecessor can participate. This
benchmark setting does not change the production 512-bit ceiling. Fixture
certificates are preparation evidence; they are never supplied to the measured
constructor as hints.

The interpreted probes live in
[`ProofProbe/PMinusOne`](../bench/HexPrimality/ProofProbe/PMinusOne/Support.lean).
They execute each distinct corpus input once, through fresh-module `#eval`,
without an embedded timer. The [shared-runner manifest](../scripts/bench/pminusone_proof_sweep.py)
compares disabled/enabled family modules in eight adjacent, alternating rounds
and subtracts the same-round import-only baseline. All 60 inputs participate;
the seven successful 128-bit parents are separated from the three exhausted
parents before measurement. This is search phase attribution, not kernel
replay. Native construction retains per-input LeanBench timings.

Ordinary factorization uses the larger-factor table and seeds 0 through 4.
Both arms retain the production rho, stage-1, ECM, and worklist allocations.
Enabled continuation can use one additional counted attempt from spare caller
fuel, for at most nine smooth attempts rather than eight. Every total timing
includes this extra work. If fuel is at most eight, continuation is skipped
and the original routes receive their complete allocation.

## Four-slot ordinary allocation diagnostic

The four-slot allocation, which charges continuation against the stage-1
budget, is recorded in the [factorization summary](bench-results/pminusone-factor-summary.json)
accounts for all 4,880 samples: 61 inputs, five fixed seeds, and eight adjacent
AB/BA blocks. It lists the 31 contributing collections and their hashes.
The disabled policy completes 205 checked input/seed pairs; the enabled policy
completes 200, with no gains and five losses.

The [ordinary regression controls](bench-results/pminusone-factor-controls.jsonl.gz)
contain eight adjacent AB/BA blocks for each input and seed, with all 2,480
samples retained. All 155 checked baseline successes are retained. Ratios
compare enabled and disabled median total times within each family.

| Family | Input/seed pairs | Checked, disabled | Checked, enabled | Time ratio |
|---|---:|---:|---:|---:|
| Balanced | 35 | 35 | 35 | 0.969 |
| Smooth | 40 | 40 | 40 | 0.987 |
| Table | 80 | 80 | 80 | 1.004 |

The extra-prime families use the prescribed larger factors. Successful-family
timings require checker acceptance in both arms and an actual continuation on
the target cofactor. The 512-bit opportunity family has no checked completions,
so it has no successful-factorization timing ratio.

| Family | Input/seed pairs | Checked, disabled | Checked, enabled | Time ratio |
|---|---:|---:|---:|---:|
| 128-bit opportunities | 35 | 35 | 35 | 1.008 |
| 256-bit opportunities | 35 | 10 | 10 | 1.014 |
| 512-bit opportunities | 35 | 0 | 0 | — |
| 128-bit full continuation misses | 15 | 5 | 0 | 0.999 |
| 256-bit full continuation misses | 15 | 0 | 0 | 0.623 |
| 512-bit full continuation misses | 15 | 0 | 0 | 0.782 |

The miss-control ratios include exhaustion times and do not establish
successful-factorization speedups. Regression timing limits pass, but no
successful opportunity family reaches the 0.90 usefulness threshold.

The ordinary retention gate has a concrete counterexample independent of
wall-clock noise: the 128-bit `q = 8191` fixture
`170141183561861700765677798001080840267`. All five fixed seeds complete a
checked factorization with the disabled policy and exhaust with the enabled
policy. The disabled trace reaches base 2 at stage-1 bound 9999 and finds
`277827051595988963`. The enabled trace instead spends that slot on the
`(64,4096)` continuation, evaluates all 546 interval primes without a factor,
and exhausts four ECM curves at bounds 64, 512, 4096, and 9999. The seed-0
attempt totals are 52 for checked completion and 16 for exhaustion. This is a
budget-allocation loss, not evidence that a different modular backend would
restore the displaced stage-1 call. The production opt-in allocation preserves that bound-9999 call and the
ECM allocation, using a separate continuation slot. Conformance pins the
counterexample, full-miss trace, random-state preservation, and fuel ceiling.

## Native construction

The [native construction summary](bench-results/pminusone-construction-native-summary.json)
checks all 960 samples: eight adjacent AB/BA blocks for each of 60 inputs.
Every checked baseline certificate is retained: 30 inputs succeed with each
policy, with no gains or losses. The extra-prime timing rows include only
inputs that produce checked certificates in both arms and execute a
continuation on the intended predecessor cofactor.

| Family | Inputs | Checked, disabled | Checked, enabled | Time ratio |
|---|---:|---:|---:|---:|
| 64-bit extra-prime predecessors | 10 | 10 | 10 | 0.981 |
| 128-bit extra-prime predecessors | 10 | 7 | 7 | 0.510 |
| 256-bit extra-prime predecessors | 10 | 0 | 0 | — |
| 512-bit extra-prime predecessors | 10 | 0 | 0 | — |
| Full continuation misses | 2 | 0 | 0 | 0.999 |
| Balanced composites | 3 | 0 | 0 | 0.970 |
| Smooth primes | 6 | 6 | 6 | 1.003 |
| Table primes | 7 | 7 | 7 | 0.999 |

The native usefulness gate passes on the successful 128-bit family, and all
regression families satisfy the 1.10 limit. The full-miss controls are
secp256k1 and P-384; their enabled traces contain respectively 96 and six
continuations, all returning `noFactor`. Their times measure exhaustion,
not certificate production. Balanced inputs measure composite rejection.
The four-input field corpus produces no certificates in either arm and does
not establish usefulness. Native construction's verdict is independent of
the interpreted construction path and ordinary factorization; it alone does
not enable the construction default.

## Whole-module construction diagnostic

The [interpreted summary](bench-results/pminusone-construction-interpreted-summary.json)
covers all 960 samples in the
[fresh-module collection](bench-results/pminusone-construction-interpreted.jsonl.gz).
Its unadjusted wall clock includes the complete `lake build` of the probe module;
the separately recorded search clock is diagnostic only. The same 30 inputs
produce checked certificates with both policies, with no gains or losses.

| Family | Checked, disabled | Checked, enabled | Wall-time ratio |
|---|---:|---:|---:|
| 64-bit extra-prime predecessors | 10 | 10 | 0.997 |
| 128-bit extra-prime predecessors | 7 | 7 | 1.003 |
| 256-bit extra-prime predecessors | 0 | 0 | — |
| 512-bit extra-prime predecessors | 0 | 0 | — |
| Full continuation misses | 0 | 0 | 1.054 |
| Balanced composites | 0 | 0 | 1.012 |
| Smooth primes | 6 | 6 | 1.003 |
| Table primes | 7 | 7 | 1.007 |

Regression limits pass, but neither successful extra-prime family reaches the
0.90 usefulness threshold and there are no additional checked successes.
The unadjusted whole-module comparison misses the usefulness threshold; it
cannot serve as the interpreted search gate. This does not establish that interpreted search
itself failed to improve. On the seven successful 128-bit inputs, the
diagnostic search-clock medians are 84.858 ms disabled and 70.435 ms enabled
(ratio 0.830), while the fresh-module wall medians are 1.443 s and 1.447 s.
The native search medians on the same inputs are 37.921 ms and 19.356 ms.
Module-build overhead dominates the interpreted acceptance clock and masks
the much smaller search saving. These in-process diagnostic clocks are not
release-quality proof-track evidence under the shared benchmarking contract.
A matched import-only baseline and compliant fresh-module phase attribution
are needed to assess the interpreted search improvement independently of that
fixed overhead; the present collection contains no such baseline.

The retained policy collections use `checked` as the success criterion.
Their raw `outcome: "exhausted"` is a generic failed-search label, including
the known balanced composites. Their times are rejection controls, not
successful-certificate timings. The benchmark diagnostics preserve the
producer's distinct composite, exhausted, incomplete, zero, and rejected
outcomes; the retained measurements and their hashes are unchanged.

## Validation

The full `lake build` passes. The affected conformance modules and both native
benchmark executables also build explicitly. The 17 upstream and one downstream
stage-2 benchmark registrations pass `verify`; the dependency checker passes.
The independent arithmetic checker validates 2,925 retained samples covering
493 distinct deterministic executions. The conformance tests include a complete
checker-accepted factorization reached through stage 2 with rho disabled, as
well as preservation of its route trace when certification fuel is exhausted.

```sh
lake build
lake build hexprimality_bench hexintfactor_bench \
  HexPrimality.Conformance HexPrimality.ConstructionConformance \
  HexIntFactor.Conformance HexIntFactor.PrimalityConformance
.lake/build/bin/hexprimality_bench verify --filter Stage2.
.lake/build/bin/hexintfactor_bench verify --filter Stage2.
python3 scripts/check_dag.py
python3 scripts/bench/check_pminusone_measurements.py \
  reports/bench-results/pminusone-phases-native.jsonl.gz \
  reports/bench-results/pminusone-trace-native.jsonl.gz \
  reports/bench-results/pminusone-cap-native.jsonl.gz \
  reports/bench-results/pminusone-preparation-native.jsonl.gz
```
