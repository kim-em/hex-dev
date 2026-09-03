# HexNumberFieldTower Performance Report

`HexNumberFieldTower` is a compiled-track library: every operation it
advertises is Mathlib-free executable computation, so all of its Phase-4
evidence is ordinary LeanBench evidence and none of it is fresh-module proof
evidence (`PLAN/Phase4.md` §Evidence tracks). This snapshot records that
evidence as measured on the reference host; `libraries.yml` records the
library's phase. Four surfaces still lack an admissible ordered
mode, so the library remains at Phase 3.

## Bench targets

The compiled Mathlib-free driver is `bench/HexNumberFieldTower/Bench.lean`.
It registers ten controlled parametric targets and 39 fixed targets (49 total).
Six parametric models supply admissible mode-1 evidence. Negation, inversion,
division, and the dense single-call `toPrimitive` registration remain
executable diagnostics without an admissible mode. Seven composite surfaces
have independently justified mode-3 registrations.

| target | controlled timed operation | mode-1 model |
|---|---|---|
| `runOfQAdjoinLadder` | checked rational presentation construction at degree `n` | `n` |
| `runTowerAddLadder`, `runTowerSubLadder`, `runTowerSMulLadder` | coordinatewise work in `ℚ(√2, 3^(1/n))`, dimension `D = 2n` | `n` |
| `runTowerMulLadder` | schoolbook convolution and recursive reduction | `n²` |
| `runFromPrimitiveLadder` | apply `fromPrimitive` to all `D` primitive basis vectors | `n⁴` |

One `fromPrimitive` Horner evaluation performs `D` tower operations of
`Θ(D²)` each, hence `Θ(D³)` per vector and `Θ(D⁴)` for the full basis. A dense
`toPrimitive` call has an `O(D²)` rational-operation bound. The replacement
registration prepares a bounded-height element with all `D` coordinates
nonzero, then times one public call and its lower-order linear structural hash.
Its preregistered quadratic wall model is nevertheless inconclusive because
the flattening's primitive-basis images have dimension-dependent rational
height; it remains a binding diagnostic rather than mode-1 evidence.

The following seven registrations are mode-3 performance evidence. Their
ceilings bound the inclusive child—startup, prepared/cached fixture, discarded
warmup, auto-tuned batch, and measured calls—not merely an internal timer.

| target | canonical input | zero-grace ceiling |
|---|---|---:|
| `runAdjoin` | adjoin the fourth root of two to `ℚ(√2)` | 3 s |
| `runAdjoinIdentity` | re-adjoin `√2` to `ℚ(√2)` | 1 s |
| `runFactorRecursive` | factor over `ℚ(√2, √3)` through the intermediate field | 2 s |
| `runTowerCheckFactorization` | checked replay of the degree-24 Selmer factorization | 2 s |
| `runTowerFactorLadder` | `X^24 - X - 1` over `ℚ(√2)` | 2 s |
| `runSplit` | `(X² - 2)(X² - 3)`, producing two genuine extensions | 1 s |
| `runFlatten` | the dimension-four tower `ℚ(√2, √3)` | 1 s |

All other fixed registrations are deliberately narrower evidence.
`runOfQAdjoin`, `runToPrimitive`, and the fixed arithmetic cases are
expected-hash anchors; in particular, the cheap dimension-four `runNeg` and
`runDiv` cases do not cover their unresolved performance surfaces.
`runFactorRetry` forces a real bad first shift and is a branch/hash anchor.
`runOneLevelNorm`, `runShiftSearch`,
`runFactorRat`, `runCheckFactorization`, `runBasisImages`,
`runCertifies`, `runCoordinateMaps`, `runRecoverPair`, and
`runRecoverSearch` are correctness or attribution anchors. The twelve
Lean/PARI registrations are comparator endpoints and
`runPariNfFactorOverhead` is a protocol control. Hash agreement, branch
exercise, attribution, protocol cost, and comparator agreement are never
counted as performance modes.

### Fixture control

The add/subtract/negate/scalar/multiply and map ladders use checked
presentations with bounded-height coordinates. Inversion and division use the
height-two family `ℚ(3^(1/n), √2)`: the varying lower presentation is built
directly, then the fixed quadratic top level is admitted through `adjoin?`.
This keeps certification outside the timed body while forcing top-level xgcd
to recurse into the degree-`n` lower field. Dense coordinate numerators cycle modulo 11 and
denominators modulo 6, so every common denominator divides 60: dimension
varies while coefficient height stays bounded. This replaces the former
index-dependent denominators, whose least common multiple had growing bit
length and invalidated a dimension-only model.

Fixture construction certifies just the positive root of `X^n - 3`.
Integer Newton iteration supplies an untrusted Mahler-precision dyadic seed;
HexRoots' `isolateOne?` certifies that the local region contains exactly one
simple root. This avoids refining and pairwise separating all other roots for
an untimed fixture. Certificates, checked irreducibility, adjoining, and
flattening used to prepare inputs stay outside the timed operation.

The factor family uses Selmer trinomials `X^n - X - 1` over `ℚ(√2)`.
Rational coefficients make the shift-zero norm a square, so the canonical
factor case genuinely retries before accepting a squarefree degree-48 norm,
recursively factors it over `ℚ`, recovers factors by gcd, and checks the
result. The explicit retry anchor and independently budgeted height-two
recursive case confirm both control-flow paths.

### Scientific ranges and host protocol

Coordinatewise add/subtract/scalar multiplication use `n = 1, 2, 3, 4, 6`;
multiplication extends through `8, 12`. The failed negation family uses
`4, 6, 8, 12, 16, 24, 32, 48`, and the failed recursive inversion/division
family uses `2, 3, 4, 6, 8, 12`.
Presentation construction uses `2, 3, 4, 6, 8, 12, 16, 24`, and the
dense `toPrimitive` and full-basis `fromPrimitive` closures use
`2, 3, 4, 5, 6, 9`. Every parametric
rung uses a warm child-side batch
auto-tuned to 100 ms and five independent outer trials. The explicit
`signalFloorMultiplier := 1.0` is appropriate because process spawn is
outside the timed body; the exports retain the spawn floor and every trial.

The original final exports were pinned to logical CPU 19, with SMT sibling 67.
The dense `toPrimitive` export was pinned to logical CPU 1 (SMT sibling 49)
and records clean pre-rebase preregistration commit `5f4bab2fc` (now
`c60b65dce`). For the original CPU 19 protocol, a three-second `/proc/stat`
postflight sample measured 1.33% busy on each sibling; load averages were 1.28,
2.53, and 2.87 on a 96-logical-CPU host. This is a postflight protocol check,
not a claim that the host was idle throughout.

```sh
taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runOfQAdjoinLadder \
  Hex.NumberTowerBench.runTowerAddLadder \
  Hex.NumberTowerBench.runTowerSubLadder \
  Hex.NumberTowerBench.runTowerSMulLadder \
  Hex.NumberTowerBench.runTowerMulLadder \
  Hex.NumberTowerBench.runFromPrimitiveLadder \
  --outer-trials 5 --export-file <mode1.json>

taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerNegLadder \
  Hex.NumberTowerBench.runTowerInvLadder \
  Hex.NumberTowerBench.runTowerDivLadder \
  --outer-trials 5 --export-file <unresolved-diagnostics.json>

taskset -c 1 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runToPrimitiveLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-dense-to-primitive-5f4bab2f-chungus2-cpu1.json

taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runAdjoin \
  Hex.NumberTowerBench.runAdjoinIdentity \
  Hex.NumberTowerBench.runFactorRecursive \
  Hex.NumberTowerBench.runTowerCheckFactorization \
  Hex.NumberTowerBench.runTowerFactorLadder \
  Hex.NumberTowerBench.runSplit \
  Hex.NumberTowerBench.runFlatten \
  --repeats 5 --export-file <mode3.json>
```

### Parametric verdicts

| target | schedule | verdict | normalized slope | normalized-cost range | worst spread | artefact |
|---|---|---|---:|---:|---:|---|
| `runOfQAdjoinLadder` | 2, 3, 4, 6, 8, 12, 16, 24 | **consistent** | −0.119 | 165.08–211.08 | 3.03% | original mode-1 |
| `runTowerAddLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.076 | 223.25–240.79 | 2.72% | original mode-1 |
| `runTowerSubLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.072 | 223.97–240.34 | 2.25% | original mode-1 |
| `runTowerSMulLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.046 | 300.38–316.54 | 2.69% | original mode-1 |
| `runTowerMulLadder` | 1, 2, 3, 4, 6, 8, 12 | **consistent** | +0.096 | 3,866.98–4,394.58 | 3.96% | original mode-1 |
| `runFromPrimitiveLadder` | 2, 3, 4, 5, 6, 9 | **consistent** | −0.026 | 8,393.62–8,775.98 | 11.89% | original mode-1 |
| `runToPrimitiveLadder` | 2, 3, 4, 5, 6, 9 | **inconclusive** | +1.023 | 985.30–3,802.84 | 23.29% | dense forward-map diagnostic |

The first six rows use their original source-derived models with LeanBench's
default slope tolerance. No intercept was added and no tolerance was widened
after measurement. The last row uses the quadratic model committed before its
official run. Its per-call medians rise from 3.695 µs at `n = 2` to
308.030 µs at `n = 9`; the +1.023 residual is one empirical power above the
quadratic model over this schedule. It is reported only as the failed-model
residual, not adopted as a replacement exponent. The nonmonotone medians at
`n = 5` (45.118 µs) and `n = 6` (38.680 µs) further show that the exact
primitive presentation, not dimension alone, affects the wall cost.

### Ordered-mode assessment

Before selecting absolute budgets, executable diagnostics attempted the
natural degree/factor-count parameter for every composite surface:

| surface | attempted schedule and observed result | ordered-rule conclusion |
|---|---|---|
| negation | the certified one-level schedule through dimension 48 gives β = −0.162 against linear | sub-microsecond fixed overhead can explain the weak negative slope, but no honest corrected model or canonical hard input is established: mode 4 |
| inversion | the reordered checked height-two family `ℚ(3^(1/n), √2)` completes through `n = 12` but gives β = +0.522 against `n² log n` | removing relative-factorization fixture growth does not repair the timed model: mode 4 |
| division | the same genuine-recursion family completes through `n = 12` but gives β = +0.748 against `n² log n`; the earlier tower order gave +0.594 | stable contrary evidence on two certified families: mode 4 |
| dense `toPrimitive` | one prepared all-nonzero input at each `D = 2n` rung rejects the preregistered quadratic model with β = +1.023 | `QAdjoin.add` and `QAdjoin.smul` perform the expected `Θ(D²)` rational operations, but the primitive-basis image heights vary with dimension and exact-rational normalization adds an unmodelled bit-cost term: mode 4 |
| adjoin | degrees 2, 3, 4, 6, 8: 13.7 ms, 35.5 ms, 98.1 ms, 804.5 ms, 4.71 s; degree 12 hit 30 s | isolation, factor selection, and validation change dominance |
| identity adjoin | degrees 2, 3, 4: 18.0 ms, 2.37 s, 1.68 s; degree 6 hit 30 s | branch-sensitive recovery is nonmonotone |
| recursive relative factorization | Selmer degrees 2, 3, 4, 6 over a height-two tower take 7.598, 12.320, 18.591, and 46.578 ms, giving β = +0.636 against the attempted linear model | the recursive level changes the gcd/resultant/replay mixture |
| checked replay | degrees 2 through 24: 0.404 ms through 126.3 ms; linear residual +1.485 | squarefree, gcd, and replay work do not admit the candidate wall model |
| factor | degrees 2 through 24; local exponents rise 0.80 to 4.48 | gcd/resultant/replay shares change with coefficient growth |
| split | factor-count 1 is excluded from the verdict; the eligible 2-to-3 jump is 68.3 ms to 1.89 s (27.7×) | repeated factor/isolate/adjoin phases change dominance |
| flatten | top degrees 1, 2, 3, 4: 0.96 ms, 21.0 ms, 107.7 ms, 460.4 ms | eliminant/isolation/recovery phases change dominance |

The diagnostics are retained executable measurements, not informal timing
notes. The first four rows cannot advance past mode 4: their cheap fixed
dimension-four anchors are neither canonical hard inputs nor meaningful
operation-specific ceilings. The remaining seven composite surfaces have no
tight independently justified mode-1 model and no published bound covering
their inclusive dominant isolation/gcd/replay mixture; their canonical
mode-3 budgets are therefore the next ordered choice.

| target | per-call median | median auto-tuned batch | ceiling | result |
|---|---:|---:|---:|---|
| `runAdjoin` | 311.405 ms | 311.405 ms | 3 s | hash match, under ceiling |
| `runAdjoinIdentity` | 18.084 ms | 289.345 ms | 1 s | hash match, under ceiling |
| `runFactorRecursive` | 7.919 ms | 253.393 ms | 2 s | hash match, under ceiling |
| `runTowerCheckFactorization` | 124.730 ms | 249.460 ms | 2 s | hash match, under ceiling |
| `runTowerFactorLadder` | 249.758 ms | 249.758 ms | 2 s | hash match, under ceiling |
| `runSplit` | 68.203 ms | 272.813 ms | 1 s | hash match, under ceiling |
| `runFlatten` | 20.819 ms | 333.110 ms | 1 s | hash match, under ceiling |

These seven ceilings were chosen from the completed diagnostic schedule and the
canonical input before the final five-repeat export; the export directly
checks the inclusive whole-child ceilings with zero grace. The ceiling applies
to the whole child, while the batch column shows the actual auto-tuned work
performed in each measured repeat; the small per-call medians are not presented
as the available budget headroom. In table order the whole-child ceiling to
measured-batch margins are 9.63×, 3.46×, 7.89×, 8.02×, 8.01×, 3.67×,
and 3.00×. The in-process `verify` command checks benchmark bodies and hashes,
not these process-level deadlines; the inclusive ceilings are enforced by the
recorded `run` export protocol.

### Ordered Trager assessment

The canonical raw profile uses one whole-thread denominator: 58.24% lies inside
`factor?`, while gcd occupies 47.28%, checked replay 29.40%, shift search
29.63%, rational factorization 23.96%, resultant work 4.21%, recovery 3.60%,
and `Hex.ZPoly.factorize` only 1.42%. The mechanical ratios against the resolved
`factor?` frame are 1.42 / 58.24 = 2.44% for integer factorization and
47.28 / 58.24 = 81.18% for gcd. They are useful only as attribution signals:
roughly 40% of the raw capture is GMP stack-unwind truncation rather than
process setup, so nonuniform missing ancestors can bias exact ratios. The
conclusion does not depend on either renormalized percentage: integer
factorization is a small whole-capture phase, while gcd alone dominates the
resolved target frame. The earlier filtered 5.26% used another denominator and
is not compared directly.

Consequently the cited BHKS bound covers only a small integer-factorization
subphase, not the inclusive dominant rational-polynomial gcd, resultant,
shift, and executable replay work. It cannot justify mode 2. The degree-24
Selmer trinomial is the top completed diagnostic rung and the canonical hard
one-level input for the enforced 2 s mode-3 ceiling. The separate
`runFactorRecursive` mode-3 case factors `X² - X - 1` over
`ℚ(√2, √3)`, forcing a non-short-circuit recursive relative factorization
through the intermediate field. This selection preserves the SPEC's recurrence
as a worst-case contract; it does not relabel that recurrence as a measured
wall model.

### Smoke cost

The merge-facing `verify` command exercises all 49 registrations and keeps
the single-root fixture optimization, so comparator rungs remain inside the
repo-wide smoke budget. With the cypari2 driver enabled it passes locally.
Inconclusive parametric diagnostics do not make `verify` fail: they are
retained measurements, not accepted modes. No hash, oracle, or comparator
check substitutes for the performance modes above.

## Comparator ratios

The library SPEC declares one external comparator,
**PARI/GP nffactor via cypari2**, class `informational`, scoped to the
`factor?` bench targets. `nffactor(nfinit f, t)` is the callable PARI unit
surface for factoring a
polynomial over a number field, the semantic task of `factor?` at one level.
It is wired as a persistent-subprocess process call through
`scripts/oracle/pari_bench_driver.py` and `Hex/BenchOracle/Pari.lean`
(`nf`/`factor_degrees`), with per-rung fixed Lean/PARI registration pairs on
identical deterministic Selmer inputs over `ℚ(√2)` and both sides configured
with `warmupFirstIter` and a 0.2 s `minTotalSeconds` floor so per-rung ratios
compare steady-state medians on the same basis. `libraries.yml` declares no
second comparator, so `SPEC/benchmarking.md` §Headline reports requires no
comparator-runtime plot, and the SPEC states no performance goal against
this comparator, so no gating-goal verdict applies.

**Differential correctness.** Both sides hash the sorted factor
degree/multiplicity multiset, the representation-free observable a
factorization over two different field presentations shares. Every one of the
six rungs agrees (hashes `0x91a80e0030157d88`, `0x564b7c1b2bee61fa`,
`0x2c83a4cef9799294`, `0x49213ee8f422ba78`, `0x9621b9eb5cafb441`,
`0x803ff6b97716ffb9` at `n = 2, 3, 4, 6, 8, 12`), which makes the comparator
a cross-implementation conformance check as well as a timing one.

**Per-call overhead.** `runPariNfFactorOverhead` issues one `nf`-family
request whose PARI-side work is a constant `0`, so it measures the JSON
request/reply round trip alone. Its median is **6.185 µs** (min 6.139 µs,
max 6.290 µs across three repeats). Overhead is at most 29.2% of the PARI
wall time (at `n = 2`) and 8.7% at its lowest (`n = 6`), so every rung clears
the 50% eligibility floor, and every per-call wall time is far inside the
10 s hard ceiling and 1 s soft target: all six rungs are eligible. Overhead
exceeds 5% of PARI wall time on every rung, so both raw and
overhead-adjusted ratios are recorded; the adjusted figure subtracts only the
request/reply floor, leaving serialization and PARI-side `nfinit`/polynomial
construction charged to PARI.

Export (clean `3f23d6425` bench sources; PARI 2.17.2 via cypari2 2.2.4):

```sh
HEX_PARI_BENCH_PYTHON=/tmp/hex-9727-pari-venv/bin/python3 \
taskset -c 13 .lake/build/bin/hexnumberfieldtower_bench run \
  <the six runTowerFactorPair* / runPariNfFactor* pairs> \
  Hex.NumberTowerBench.runPariNfFactorOverhead \
  --export-file reports/bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json
```

Ratios are quoted as PARI wall time divided by Hex wall time, so a value
above 1 would mean Hex is faster.

| n | Hex `factor?` | PARI `nffactor` | overhead share of PARI | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---:|---:|
| 2 | 1.015 ms | 21.173 µs | 29.2% | 0.0209 | 0.0148 |
| 3 | 1.378 ms | 24.501 µs | 25.2% | 0.0178 | 0.0133 |
| 4 | 1.979 ms | 27.567 µs | 22.4% | 0.0139 | 0.0108 |
| 6 | 3.425 ms | 70.718 µs | 8.7% | 0.0206 | 0.0188 |
| 8 | 5.947 ms | 33.777 µs | 18.3% | 0.0057 | 0.0046 |
| 12 | 16.180 ms | 55.113 µs | 11.2% | 0.0034 | 0.0030 |

### Trend

PARI is faster at every rung, from 48x at `n = 2` to 294x at `n = 12` (68x
to 331x overhead-adjusted), and the ratio widens as the parameter grows.
Fitting each side's growth over the six rungs: Hex's median grows as about
`n^1.5` overall, with its top-octave local exponent near 2.5; PARI's net
cost (overhead subtracted: 15.0, 18.3, 21.4, 64.5, 27.6, 48.9 µs) grows as
about `n^0.7`, with a discontinuous spike at `n = 6` (64.5 µs against 27.6 µs
at `n = 8`) that is PARI-side input dependence, not a trend point; no claim
here rests on it. A sub-linear net exponent means PARI's arithmetic at these
degrees is still partly masked by its own per-call object construction, so
the divergence is a lower bound on the structural gap.

This diverging trend is the declared expectation, not an adverse finding:
the SPEC classifies the comparator `informational` precisely because PARI
runs `nffactor` over `nfinit`'s absolute integral-basis presentation with
maximal-order machinery, a structurally different pipeline from Hex's
relative one-level Trager norms with checked replay (the §Profile capture
shows about 41% of the Hex call inside the executable certificate check
alone, work PARI does not perform). The ratio is recorded for orientation
and does not gate Phase 4.

### Absence declarations retained

The per-library SPEC declares the remaining surfaces with no comparable PARI
unit surface, all with the reason
`no-comparable-surface-in-named-comparator`, and this report changes none of
them: tower element arithmetic (`Elem` add/sub/neg/mul/inv/div/smul; PARI's
`nfelt*` operations act on absolute integral-basis coordinates, and nested
`t_POLMOD` towers are not a supported arithmetic surface for inversion), and
adjoining, splitting, and flattening (`nfsplitting`, `polcompositum`, and
`rnfequation` return abstract defining polynomials up to isomorphism, not
the fixed-embedding root selection, coordinate maps, or validated tower
level these units produce). The measurements above cover exactly the
`factor?` surface PARI does expose.

## Profile

samply 0.13.1 sampled at 999 Hz on the same `chungus2` hardware (Linux
x86-64 6.12.100, AMD EPYC 9455 48-Core Processor, 96 logical CPUs), Lean
4.34.0-rc2, and LeanBench 0.1.0. Every fixture is deterministic and no runtime
oracle participates in any profiled route. Multiplication retains its earlier
timed-region-filtered capture from binary `d9fc6d73f`; its algorithm code is
unchanged. Recursive inversion was refreshed from clean binary `8ea8d6819`
on the reordered genuine-recursion family. Dense `toPrimitive` was refreshed
from clean pre-rebase commit `6a4911dbb` (now `aad8c23bf`) after its quadratic
model failed. The
factorization family was refreshed from the
pre-rebase binary `5d4cb88ad` (bench source byte-identical to `7ad34c201`) at
its canonical mode-3 degree-24 input. The commands were:

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerMulLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerInvLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runToPrimitiveLadder  9 5000000000
samply record --save-only --no-open --rate 999 --unstable-presymbolicate \
  -o /tmp/hex-profile-runTowerFactorMode3-5d4cb88a-fixedraw.json.gz -- \
  .lake/build/bin/hexnumberfieldtower_bench _child \
  --bench Hex.NumberTowerBench.runTowerFactorLadder --fixed \
  --min-total-nanos 5000000000 --repeat-index 0
```

Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexnumberfieldtower_bench`.
Raw `*.json.gz` artefacts stay developer-local under `/tmp` as
`SPEC/profiling.md` requires; the committed summary artefacts are listed in
§Artefact traceability.

The lean-bench child emits no timed-region sidecar for fixed dispatch, so
the orchestrator cannot filter fixed registrations; this is the same scope
condition the merged HexBerlekampZassenhaus report records for its fixed-only
family. The fixed-only families (`trager-factorization`, `adjoin-extend`, and
`split-flatten`) are therefore covered by whole-bench-thread raw samply
captures of the fixed-mode child over a long auto-tuned batch
(`_child --bench <case> --fixed --min-total-nanos 5000000000`), analysed
with the same categorizer. The adjoin/split/flatten target frames carry 95.71%,
99.90%, and 97.93% of their respective threads. The refreshed factor target
carries 58.23% of the whole thread and is still the single dominant resolved
frame. Most of the remainder consists of GMP leaves whose ancestors were lost
to stack-unwind truncation; it must not be labelled process setup. Its phase
percentages below therefore retain the deliberately unfiltered denominator,
and renormalized target-frame ratios are only qualitative. Raw captures carry
no lean-bench-samply calibration/sensitivity diagnostics, which is the
declared scope of fixed-family profile coverage.

| family | case | retained / rejected | calibration residual | leaf cost | classified |
|---|---|---:|---:|---|---:|
| `tower-coordinate-arithmetic` | `runTowerMulLadder` n=12 | 4,957 / 237,605 | 0.700 ms | allocation 39.72%, Lean runtime 31.07%, GMP 23.56%, own code 4.80% | 99.15% |
| `tower-coordinate-arithmetic` | `runTowerInvLadder` n=12 | 4,257 / 66 | 0.509 ms | GMP 58.73%, Lean runtime 20.74%, allocation 19.83%, own code 0.61% | 99.91% |
| `split-flatten` | `runToPrimitiveLadder` n=9 | 3,651 / 124,055 | 0.870 ms | GMP 44.67%, allocation 38.84%, Lean runtime 15.09%, own code 0.60% | 99.21% |
| `trager-factorization` | `runTowerFactorLadder` degree 24 (raw fixed capture) | 16,325 / n.a. | n.a. | GMP 74.54%, Lean runtime 15.34%, allocation 9.21%, own code 0.78% | 99.87% |
| `adjoin-extend` | `runAdjoin` (raw fixed capture) | 13,786 / n.a. | n.a. | allocation 46.44%, GMP 27.26%, Lean runtime 24.05%, own code 2.01% | 99.75% |
| `split-flatten` | `runSplit` (raw fixed capture) | 9,985 / n.a. | n.a. | Lean runtime 40.01%, allocation 37.91%, GMP 13.52%, own code 7.83% | 99.27% |
| `split-flatten` | `runFlatten` (raw fixed capture) | 18,762 / n.a. | n.a. | allocation 37.74%, Lean runtime 37.06%, GMP 20.47%, own code 4.47% | 99.74% |

The three retained filtered captures pass calibration (residuals 0.51 to 0.87 ms
against the 5 ms limit), retained-sample minimums, and the ±5 ms
sensitivity check. The large rejected count on the multiplication capture is
the untimed `m = 12` tower-fixture prelude. Likewise, the dense
`toPrimitive` capture's 124,055 rejected samples are its untimed dimension-18
`flatten?` preparation. Both preludes are excluded by construction.

### `tower-coordinate-arithmetic`: attributes cleanly

Multiplication at dimension 24: 100% of retained samples inside the
registered target, 99.92% in `Hex.NumberTower.mul` →
`Arithmetic.mulCoords`, splitting into `Arithmetic.convolve` (81.76%) and
the recursive top-down `Arithmetic.reduce`/`reduceCoeffs` (58.34%/56.93%,
overlapping inclusive shares). That is exactly the derivation at the
registration site: mixed-radix convolution plus reduction by each monic
defining polynomial. Recursive inversion at dimension 24: 91.59% in
`Hex.NumberTower.inv`/`Arithmetic.invCoords`, dominated by the extended
gcd `Hex.DensePoly.xgcdLeftAux` (85.46%) whose inner work is polynomial
division (`DensePoly.divMod` 63.61%) and tower multiplication
(`mulCoords` 57.58%, with add/sub at 30.73%/23.96%). The capture verifies that
the reordered family measures the intended recursive exact-field Euclidean
chain. Both phases named by the SPEC's arithmetic
section are the measured cost; nothing is unattributed.

### `trager-factorization`: certificate and gcd machinery, not BZ

On the canonical degree-24 input, 58.24% of whole-thread samples are inside
`Hex.NumberTower.factor?` (`factorSquarefree?` 57.57%). Inclusive shares of
the same whole-thread denominator are `Hex.DensePoly.gcdAuxImpl` 47.28%, the
replay/irreducibility certificate `Factor.check`/`Factor.isIrreducible`
29.40%/29.37%, the bounded shift search `Norm.findSquarefreeShiftAux` 29.63%
with `Norm.isSquarefree` 23.20%, the rational base case `Factor.factorRat?`
23.96%, resultant machinery (`DensePoly.resultantOrdered` 4.21%), gcd
recovery (`Factor.recover` 3.60%), and the actual integer factorization
`Hex.ZPoly.factorize` at only 1.42%. Every named phase has a
registered component case (`runOneLevelNorm`, `runShiftSearch`,
`runFactorRat`, `runCheckFactorization`, and the ladder itself), and the
underlying `DensePoly` gcd/resultant kernels carry their own asymptotic
evidence in the upstream HexPoly/HexResultant reports. The 41% certificate
share in the older degree-16 filtered capture and 29% whole-thread share here
are the executable checked-replay guarantee the SPEC mandates
(`Factorization.checked`). That deliberate structural cost, together with gcd
and shift search, is why the BHKS-only envelope cannot serve as mode 2
(§Ordered Trager assessment). Because stack-unwind loss is nonuniform, none of
these whole-capture shares is promoted to an exact within-target percentage.

### `adjoin-extend`: fixed-embedding selection dominates

95.71% of the raw capture is inside `Hex.NumberTower.adjoin?`. The dominant
phase is candidate-factor disambiguation under the fixed embedding:
`RawEvaluation.vanishesAt?` 95.46% → `Hex.AlgebraicRoot.ofEliminant?`
94.92% → the upstream isolation kernel `Hex.isolate`/`isolateLoop` 95.15%,
with `Hex.taylor` 69.37% and dyadic Gauss arithmetic (`GaussDyadic.mul`
46.63%) as the leaf work; `Internal.extend?` (level validation) is 31.88%
and factor selection `selectFactor?` 63.62%. The factorization step itself
is not visible at this input because the quartic factors immediately; the
cost is the SPEC's embedding invariant being enforced (`adjoin?` "selects
the unique irreducible factor that vanishes at the requested AlgebraicRoot
under the current embedding"). The isolation kernel that dominates is the
same `Hex.isolate` measured by HexNumberField's and HexRoots' registered
isolation ladders; its asymptotic evidence lives in those upstream reports,
and the tower-level boundary is measured end to end by the registered
`runAdjoin`/`runAdjoinIdentity` cases.

### `split-flatten`: isolation again, through both entry points

`runSplit`: 99.90% inside `Hex.NumberTower.splitAux`; root retention and
adjoining dominate through the same disambiguation path
(`RawEvaluation.vanishesAt?` 66.97%, `Hex.isolate` 64.55%), with the
remainder in the tower factorization it repeats after each extension.
`runFlatten`: 97.93% inside the target, 97.36% in
`Hex.NumberTower.flatten?`, dominated by the primitive-element candidate
search `Flatten.searchRecoveredAux` 90.20% whose cost is
`Flatten.candidateAt?` → `Hex.AlgebraicPoly.Common.shift?` 83.22% (the
integer eliminant of `θ + cα`) and the canonical exactification
`Hex.AlgebraicRoot.exact?` 61.83%, both running the upstream `Hex.isolate`
kernel (94.99%). The flattening components the search feeds are the
registered `runBasisImages`, `runCertifies`, `runCoordinateMaps`,
`runRecoverPair`, and `runRecoverSearch` cases; the eliminant/exactification
kernels are HexNumberField surfaces with their own registered evidence.

The refreshed dense `toPrimitive` capture at dimension 18 retains 97.81% of
samples in the target and 95.73% in `Flatten.toPrimitiveWith`.
`QAdjoin.add`/`DensePoly.addImpl` account for 57.98%/56.86% inclusive and
`QAdjoin.smul` for 37.63%; `Rat.add` and `Rat.mul` account for 51.88% and
35.99%. GMP is 44.67% of leaf cost, led by rational-normalization gcd work,
while the structural `ratChecksum` walk is only 1.89% inclusive. The profile
therefore confirms that all coordinates take the intended multiply/add path
and that the failed wall model comes from exact-rational bit cost in the
primitive images, not fixture preparation or result hashing.
No capture shows a dominant cost in a function the SPEC does not name as part
of the measured operation, and no audit-found issue was filed from these
captures.

### Artefact traceability

| artefact | source commit / role | host state | SHA-256 |
|---|---|---|---|
| [original mode-1 export](bench-results/hex-number-field-tower-phase4-final-mode1-ce03eb89-chungus2-cpu19.json) | clean pre-rebase `ce03eb89b` (same patch now `9a9fe1e26`); passing unaffected models | [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | `65275d1f2dfb6fd41e1a962d44d27bc843ab75ed8a2d5a305df2d2aed7c4bfbb` |
| [superseded fixed calibration](bench-results/hex-number-field-tower-phase4-final-mode3-ce03eb89-chungus2-cpu19.json) | clean pre-rebase `ce03eb89b` (same patch now `9a9fe1e26`); retained measurements, but the negation/division/forward-map rows are not admissible mode-3 evidence | [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | `391d48365634eb9cc3b02eb8801920e13034bc537777d6ebc6d5f2834769426e` |
| [superseded seven-case mode-3 export](bench-results/hex-number-field-tower-phase4-final-mode3-d277c583-chungus2-cpu19.json) | clean pre-rebase `d277c583` (same patch now `c720b4aca`); earlier canonical-case calibration retained for provenance | [matching postflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | `dcae0daaac0470764794b793606a005a83c845dd9af44a80f61ddad97e593f06` |
| [constructor-only rerun](bench-results/hex-number-field-tower-phase4-final-ofq-e63e3a589-chungus2-cpu19.json) | clean pre-rebase `e63e3a589` (same patch now `77513c3b6`); passing constructor model | [matching postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | `f703055985a9b4f25b69bd954d7072f08b505896cc1625ad7ec98e102f55f65b` |
| [extended ordered-mode diagnostic](bench-results/hex-number-field-tower-phase4-mode1-nine-and-constructor-diagnostic-d277c583-chungus2-cpu19.json) | clean pre-rebase `d277c583` (same patch now `c720b4aca`); superseded nine-case/constructor diagnostic | CPU 19 | `9bea0ee7378b3cf8b71bccb200cdf09e92085b8806ef4d19bab704c25e92b793` |
| [d277 postflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | host state paired with the d277 exports | sampled CPU and SMT sibling | `cbb9ae6f454ed300d51e10dfb01f7454b568bde45b74e6a7b033b2b55b22c8d8` |
| [e63 postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | host state paired with the constructor rerun | sampled CPU and SMT sibling | `79d70f64f57983dfed82d96732510106b5ae54aabe304c309d3e90c80f366738` |
| [repaired forward-map export](bench-results/hex-number-field-tower-phase4-to-primitive-db22ebe6-chungus2-cpu19.json) | clean pre-rebase `db22ebe6c` (now `8c5e38f39`); original cubic model after the executable zero-coordinate fix | CPU 19 | `1b835e4c87b65aa7e0c520178991ea8b6a0975a911d4c5a7b5bcc1d63c42661a` |
| [repaired forward-map profile](bench-results/hex-number-field-tower-to-primitive-profile-08c17a18-chungus2.json) | clean pre-rebase `08c17a18c` (now `bcab4e402`); timed-region-filtered dimension-18 full-basis map | CPU 19 | `56739b12f292aad4085814d206730d0c67f4337949d8603b7faf5df810ff9f18` |
| [dense forward-map export](bench-results/hex-number-field-tower-dense-to-primitive-5f4bab2f-chungus2-cpu1.json) | clean pre-rebase preregistration commit `5f4bab2fc` (now `c60b65dce`); five trials at every `n = 2, 3, 4, 5, 6, 9` rung | CPU 1 | `4e6bdf834eb2e98ead56ac84f46da08eacd78c51ecd60ecf947af67b66df36f0` |
| [dense forward-map profile](bench-results/hex-number-field-tower-dense-to-primitive-profile-6a4911db-chungus2.json) | clean pre-rebase `6a4911dbb` (now `aad8c23bf`); timed-region-filtered dimension-18 dense public map | unpinned shape capture | `5dadec1dfefc811addb7e7ae242f88d81ab3880f91a19570356e4e92402cd7f9` |
| [recursive arithmetic diagnostics](bench-results/hex-number-field-tower-phase4-recursive-arithmetic-8af75849-chungus2-cpu19.json) | clean pre-rebase `8af758494` (now `a965ee906`); checked reordered height-two family | CPU 19 | `90a52359c542a1708acb68d845daf9be5bea1ca7ce7dfaf9b467309b94024efd` |
| [negation and recursive-factor diagnostics](bench-results/hex-number-field-tower-phase4-final-mode-diagnostics-959489aa-chungus2-cpu19.json) | clean pre-rebase `959489aa2` (same patch now `eeb360ef8`); final ordered-mode attempts | CPU 19 | `1bdfb6b3f0f65808c8a1e6f2cf5698420ebb54931cdfcb1b449afc13e56dcf03` |
| [division and forward-map diagnostics](bench-results/hex-number-field-tower-phase4-final-div-map-diagnostics-dd5ef519-chungus2-cpu19.json) | clean pre-rebase `dd5ef5197` (same patch now `cb6583d3a`); final ordered-mode attempts, with its sparse `runToPrimitiveLadder` block superseded by the dense export | CPU 19 | `d965dfde3919c9eaab2f15d505b4cca43b8d0d38b95e1130db5d93901590f52a` |
| [negation calibration](bench-results/hex-number-field-tower-opus-calibration-605abcb5-chungus2-cpu19.json) | clean pre-rebase `605abcb5` (same branch state now `2ed1aba5d`); registered linear diagnostic, β = −0.162 | CPU 19 | `360bcf931e5171183ae25ddba16d6ff3edbb820bab5d40fd4c0de1908919f5a8` |
| [ordered-mode diagnostics](bench-results/hex-number-field-tower-phase4-mode3-diagnostics-b2ebf281-chungus2-cpu1.json) | clean pre-rebase `b2ebf281b` (same patch now `eaa691fc9`); temporary executable diagnostics | CPU 1 | `6f3182498feec6f8b4d7fb121f5cd67fb5b1ba011117b1e72e3431217981270d` |
| [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | final measurement protocol | sampled CPU and SMT sibling | `f8a9d1d8294f59cf1bce18e02a2baae57728c87db24f5e96cc1c5c0e884a5a76` |
| [canonical factor profile](bench-results/hex-number-field-tower-phase4-final-factor-profile-5d4cb88a-chungus2.json) | pre-rebase binary `5d4cb88ad` (same patch now `842043ebf`); algorithm source unchanged | unpinned shape capture | `f34c803bc741a92b9ac5b6040b107aa80c206f9a8b1d6515635ca6af5d3c9cf2` |
| [factor degree diagnostic](bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json) | clean `7d6c0c50a`; rejects the former envelope | CPU 13 | `c0ae3da96fe41f36a87ed6665bf98cd1b2d4c9c209b541a7a0516cbdb28f9d30` |
| [component anchors](bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json) | clean `3f23d6425`; hash/attribution only | CPU 13 | `1927e8268c5ac22a1df0e987db5dff878e7ccdcc448252d21b6ee6240689f156` |
| [PARI pairs](bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json) | clean `322f53b15`; identical comparator sources | CPU 13 | `5c60e35f20265683fff0eb01f397e3355957fcd0737f0ca21e7781a0b30f0a3f` |
| [coordinate profile summaries](bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json) | archived clean `d9fc6d73f` multiplication binary; captured multiplication source matches current `8ea8d6819` | unpinned shape capture | `31767bff125621d07391e151bc613a3a1c8ee7b74300a81fd7029af2198b505c` |
| [refreshed recursive-inversion profile](bench-results/hex-number-field-tower-recursive-inversion-profile-8ea8d681-chungus2.json) | clean `8ea8d6819`; timed-region-filtered reordered family at dimension 24 | CPU 19 | `91e67ce7b3764578fec8d2bcf7011f1ec489399871937c04442e3a4e222bbe43` |

The evidence added here comprises the single-root bounded-height fixtures,
six passing mode-1 surfaces, seven independently budgeted mode-3 surfaces,
four binding mode-4 diagnostics, explicit retry and recursive-relative branch
exercise, and an inclusive canonical factor profile. The component, protocol,
hash, and comparator exports retain only their stated roles. The unresolved
surfaces prevent a Phase-4 exit.

Toolchain: Lean 4.34.0-rc2, LeanBench 0.1.0, samply 0.13.1, PARI 2.17.2,
and cypari2 2.2.4. Reference host: `chungus2`, Linux x86-64, AMD EPYC 9455
48-Core Processor, 96 logical CPUs.

## Verification

- `lake build HexNumberFieldTower HexNumberFieldTower.Conformance
  hexnumberfieldtower_emit_fixtures`: pass.
- `lake exe hexnumberfieldtower_bench list`: 10 parametric plus 39 fixed
  registrations.
- `lake exe hexnumberfieldtower_bench verify`: all 49 registrations pass.
- Emitted Tower fixtures match the committed JSONL byte for byte; the PARI
  oracle checks 9 cases with 0 failures.
- `python3 scripts/check_phase4.py`: pass.
- `python3 scripts/check_dag.py`: pass.

## Concerns

These unresolved surfaces are tracked by #9665 and its focused follow-ups,
including #9945; #9815 is the original ordered-mode audit parent.

- Negation has no admissible evidence mode: the registered linear diagnostic
  gives β = −0.162, just outside the default two-sided gate. The
  sub-microsecond fixture is vulnerable to fixed overhead, while no canonical
  hard input gives the cheap coordinatewise operation a meaningful absolute
  budget; this remains an unresolved diagnostic, not a substantive complexity
  finding.
- Recursive inversion rejects `n² log n` with β = +0.522 on a checked
  height-two family whose fixture completes at every rung through `n = 12`.
- Division rejects the same independently derived model with β = +0.748 on
  that family, corroborating the earlier +0.594 failure in the opposite tower
  order. No independently derived executable bit-cost model accounting for
  exact-rational coefficient growth is currently recorded for either
  operation.
- Dense `toPrimitive` rejects its preregistered quadratic wall model with
  β = +1.023. The implementation performs the expected quadratic count of
  primitive-coordinate scalar/add operations, but their exact-rational
  coefficients do not have bounded bit height across the family; the profile
  attributes 44.67% of leaf cost to GMP and 95.73% inclusively to
  `Flatten.toPrimitiveWith`. No replacement exponent has been selected from
  the timings.
