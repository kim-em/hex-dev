# HexNumberFieldTower Performance Report

`HexNumberFieldTower` is a compiled-track library: every operation it
advertises is Mathlib-free executable computation, so all of its Phase-4
evidence is ordinary LeanBench evidence and none of it is fresh-module proof
evidence (`PLAN/Phase4.md` §Evidence tracks). This snapshot records that
evidence as measured on the reference host; `libraries.yml` records the
library's phase, and this report is the headline evidence for its Phase-4
exit.

## Bench targets

The compiled Mathlib-free driver is `bench/HexNumberFieldTower/Bench.lean`.
It registers ten controlled parametric targets and 38 fixed targets (48 total).
Registration comments derive each mode-1 model and record the attempted
parameterization, canonical input, and independently chosen zero-grace ceiling
for each mode-3 target.

| target | controlled timed operation | mode-1 model |
|---|---|---|
| `runOfQAdjoinLadder` | checked rational presentation construction at degree `n` | `n + 1` |
| `runTowerAddLadder`, `runTowerSubLadder`, `runTowerNegLadder`, `runTowerSMulLadder` | coordinatewise work in `ℚ(√2, 3^(1/n))`, dimension `D = 2n` | `n + 1` |
| `runTowerMulLadder` | schoolbook convolution and recursive reduction | `n²` |
| `runTowerInvLadder`, `runTowerDivLadder` | recursive extended gcd, with division adding one multiplication | `n²(log₂(n + 2) + 1)` |
| `runToPrimitiveLadder` | apply `toPrimitive` to all `D` tower basis vectors | `n³` |
| `runFromPrimitiveLadder` | apply `fromPrimitive` to all `D` primitive basis vectors | `n⁴` |

The affine model records fixed dispatch/result construction plus the linear
coordinate walk; this matters on the finite scientific range. For the map
closures, one `toPrimitive` application performs `Θ(D²)` work and all
`D` basis vectors therefore take `Θ(D³)`. One `fromPrimitive` Horner
evaluation performs `D` tower operations of `Θ(D²)` each, hence
`Θ(D³)` per vector and `Θ(D⁴)` for the full basis.

The following six registrations are mode-3 performance evidence. Their
ceilings bound the inclusive child—startup, prepared/cached fixture, discarded
warmup, auto-tuned batch, and measured calls—not merely an internal timer.

| target | canonical input | zero-grace ceiling |
|---|---|---:|
| `runAdjoin` | adjoin the fourth root of two to `ℚ(√2)` | 3 s |
| `runAdjoinIdentity` | re-adjoin `√2` to `ℚ(√2)` | 1 s |
| `runTowerCheckFactorization` | checked replay of the degree-24 Selmer factorization | 2 s |
| `runTowerFactorLadder` | `X^24 - X - 1` over `ℚ(√2)` | 2 s |
| `runSplit` | `(X² - 2)(X² - 3)`, producing two genuine extensions | 1 s |
| `runFlatten` | the dimension-four tower `ℚ(√2, √3)` | 1 s |

All other fixed registrations are deliberately narrower evidence.
`runOfQAdjoin` and the seven fixed arithmetic cases are expected-hash
anchors for mode-1-covered operations. `runFactorRetry` forces a real bad
first shift and `runFactorRecursive` forces relative factorization through
an intermediate level; both are branch/hash anchors covered inclusively by the
canonical `factor?` mode-3 case. `runOneLevelNorm`, `runShiftSearch`,
`runFactorRat`, `runCheckFactorization`, `runBasisImages`,
`runCertifies`, `runCoordinateMaps`, `runRecoverPair`, and
`runRecoverSearch` are correctness or attribution anchors. The twelve
Lean/PARI registrations are comparator endpoints and
`runPariNfFactorOverhead` is a protocol control. Hash agreement, branch
exercise, attribution, protocol cost, and comparator agreement are never
counted as performance modes.

### Fixture control

The arithmetic and map ladders use the height-two family
`ℚ(√2, 3^(1/n))`. Their dense coordinate numerators cycle modulo 11 and
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
result. The explicit retry and two-level recursive anchors independently
confirm both control-flow paths.

### Scientific ranges and host protocol

Coordinatewise arithmetic, inversion, and division use
`n = 1, 2, 3, 4, 6`; multiplication extends through `8, 12`.
Presentation construction uses `2, 3, 4, 6, 8, 12`; both map closures use
`1, 2, 3, 4, 5, 6`. Every parametric rung uses a warm child-side batch
auto-tuned to 100 ms and five independent outer trials. The explicit
`signalFloorMultiplier := 1.0` is appropriate because process spawn is
outside the timed body; the exports retain the spawn floor and every trial.

The final common export was preregistered on logical CPU 19, with SMT sibling
67. A three-second `/proc/stat` sample immediately before it measured 0.33%
and 0.66% busy; load averages were 1.29, 2.23, and 6.13 on a 96-logical-CPU
host. Both mode-1 and mode-3 commands were pinned with `taskset -c 19` and
record `git_dirty: false`. The corrected constructor validation was also
pinned to CPU 19; its three-second postflight sample measured 3.65% on both
siblings.

```sh
taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runOfQAdjoinLadder \
  Hex.NumberTowerBench.runTowerAddLadder \
  Hex.NumberTowerBench.runTowerSubLadder \
  Hex.NumberTowerBench.runTowerNegLadder \
  Hex.NumberTowerBench.runTowerSMulLadder \
  Hex.NumberTowerBench.runTowerMulLadder \
  Hex.NumberTowerBench.runTowerInvLadder \
  Hex.NumberTowerBench.runTowerDivLadder \
  Hex.NumberTowerBench.runToPrimitiveLadder \
  Hex.NumberTowerBench.runFromPrimitiveLadder \
  --outer-trials 5 --export-file <mode1.json>

taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runAdjoin \
  Hex.NumberTowerBench.runAdjoinIdentity \
  Hex.NumberTowerBench.runTowerCheckFactorization \
  Hex.NumberTowerBench.runTowerFactorLadder \
  Hex.NumberTowerBench.runSplit \
  Hex.NumberTowerBench.runFlatten \
  --repeats 5 --export-file <mode3.json>
```

### Mode-1 verdicts

| target | schedule | verdict | normalized slope | worst spread |
|---|---|---|---:|---:|
| `runOfQAdjoinLadder` | 2, 3, 4, 6, 8, 12 | **consistent** | +0.008 | 6.6% |
| `runTowerAddLadder` | 1, 2, 3, 4, 6 | **consistent** | +0.134 | 6.7% |
| `runTowerSubLadder` | 1, 2, 3, 4, 6 | **consistent** | +0.131 | 4.6% |
| `runTowerNegLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.100 | 6.5% |
| `runTowerSMulLadder` | 1, 2, 3, 4, 6 | **consistent** | +0.176 | 4.5% |
| `runTowerMulLadder` | 1, 2, 3, 4, 6, 8, 12 | **consistent** | +0.089 | 2.3% |
| `runTowerInvLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.023 | 21.3% |
| `runTowerDivLadder` | 1, 2, 3, 4, 6 | **consistent** | +0.241 | 3.3% |
| `runToPrimitiveLadder` | 1, 2, 3, 4, 5, 6 | **consistent** | n.a.¹ | 3.9% |
| `runFromPrimitiveLadder` | 1, 2, 3, 4, 5, 6 | **consistent** | n.a.¹ | 2.7% |

¹ After the leading-rung exclusion, the exact catalog model gives a bounded
normalization range but too few distinct logarithms for LeanBench to report a
slope; the verdict is still the registered two-sided normalization verdict.

The first five-trial presentation export normalized by `n` gave a stable
β = −0.153, narrowly beyond the default ±0.15 gate. That export is retained as
model-discovery evidence. Inspecting the measured constructor boundary exposes
the missing fixed dispatch/structure/generator term, the same finite-range
intercept already derived for coordinate operations. A fresh clean-commit run
against the corrected `n + 1` model gives β = +0.008. No result was discarded,
and the other nine results come from the original common export.

### Ordered mode-3 assessment

Before selecting absolute budgets, executable diagnostics attempted the
natural degree/factor-count parameter for every composite surface:

| surface | attempted schedule and observed result | ordered-rule conclusion |
|---|---|---|
| adjoin | degrees 2, 3, 4, 6, 8: 13.7 ms, 35.5 ms, 98.1 ms, 804.5 ms, 4.71 s; degree 12 hit 30 s | isolation, factor selection, and validation change dominance |
| identity adjoin | degrees 2, 3, 4: 18.0 ms, 2.37 s, 1.68 s; degree 6 hit 30 s | branch-sensitive recovery is nonmonotone |
| checked replay | degrees 2 through 24: 0.404 ms through 126.3 ms; linear residual +1.485 | squarefree, gcd, and replay work do not admit the candidate wall model |
| factor | degrees 2 through 24; local exponents rise 0.80 to 4.48 | gcd/resultant/replay shares change with coefficient growth |
| split | 1, 2, 3 quadratic factors: 19.5 ms, 68.3 ms, 1.89 s | repeated factor/isolate/adjoin phases change dominance |
| flatten | top degrees 1, 2, 3, 4: 0.96 ms, 21.0 ms, 107.7 ms, 460.4 ms | eliminant/isolation/recovery phases change dominance |

The coordinate-map diagnostic was likewise inconclusive against a linear
model (9.28 µs, 174.6 µs, 1.04 ms, 3.23 ms at `n = 1..4`), but source
inspection supplies stronger cubic/quartic full-basis models, which then pass.
For the six remaining composites, no tight independently justified mode-1
wall model emerged, and no published bound covers their inclusive dominant
isolation/gcd/replay phase mixture. Mode 2 is therefore unavailable and the
canonical mode-3 budgets are the next ordered choice.

| target | five-repeat median | ceiling | result |
|---|---:|---:|---|
| `runAdjoin` | 312.299 ms | 3 s | hash match, under ceiling |
| `runAdjoinIdentity` | 18.023 ms | 1 s | hash match, under ceiling |
| `runTowerCheckFactorization` | 124.073 ms | 2 s | hash match, under ceiling |
| `runTowerFactorLadder` | 248.941 ms | 2 s | hash match, under ceiling |
| `runSplit` | 67.342 ms | 1 s | hash match, under ceiling |
| `runFlatten` | 20.835 ms | 1 s | hash match, under ceiling |

The ceilings were chosen from the completed diagnostic schedule and the
canonical input before the final five-repeat export; the export directly
checks the inclusive whole-child ceilings with zero grace.

### Ordered Trager assessment

The canonical profile uses one whole-thread denominator: 58.24% lies inside
`factor?`, while gcd occupies 47.28%, checked replay 29.40%, shift search
29.63%, rational factorization 23.96%, resultant work 4.21%, recovery 3.60%,
and `Hex.ZPoly.factorize` only 1.42%. Relative to the resolved `factor?`
frame, integer factorization is therefore 1.42 / 58.24 = **2.44%**, while gcd
is 47.28 / 58.24 = **81.18%**. The earlier filtered 5.26% number used a
different denominator and is not compared directly.

Consequently the cited BHKS bound covers only a small integer-factorization
subphase, not the inclusive dominant rational-polynomial gcd, resultant,
shift, and executable replay work. It cannot justify mode 2. The degree-24
Selmer trinomial is the top completed diagnostic rung and the canonical hard
input for the enforced 2 s mode-3 ceiling. This selection preserves the
SPEC's recurrence as a worst-case contract; it does not relabel that recurrence
as a measured wall model.

### Smoke cost

The merge-facing `verify` command exercises all 48 registrations and keeps
the single-root fixture optimization, so comparator rungs remain inside the
repo-wide smoke budget. With the cypari2 driver enabled it passes locally in
14.1 s, down from about 45 s before the single-root fixture. No hash, oracle,
or comparator check substitutes for the performance modes above.

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
oracle participates in any profiled route. The coordinate representatives
retain the timed-region-filtered captures from binary `d9fc6d73f`; their
algorithm code is unchanged. The factorization family was refreshed from the
pre-rebase binary `5d4cb88ad` (bench source byte-identical to `7ad34c201`) at
its canonical mode-3 degree-24 input. The commands were:

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerMulLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerInvLadder     6 5000000000
samply record --save-only --no-open --rate 999 --unstable-presymbolicate \
  -o /tmp/hex-profile-runTowerFactorMode3-5d4cb88a-fixedraw.json.gz -- \
  .lake/build/bin/hexnumberfieldtower_bench _child \
  --bench Hex.NumberTowerBench.runTowerFactorLadder --fixed \
  --min-total-nanos 5000000000 --repeat-index 0
```

Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexnumberfieldtower_bench`.
Raw `*.json.gz` artefacts stay developer-local under `/tmp` as
`SPEC/profiling.md` requires; the committed summaries artefact is listed in
§Artefact traceability.

The lean-bench child emits no timed-region sidecar for fixed dispatch, so
the orchestrator cannot filter fixed registrations; this is the same scope
condition the merged HexBerlekampZassenhaus report records for its fixed-only
family. The fixed-only families (`trager-factorization`, `adjoin-extend`, and
`split-flatten`) are therefore covered by whole-bench-thread raw samply
captures of the fixed-mode child over a long auto-tuned batch
(`_child --bench <case> --fixed --min-total-nanos 5000000000`), analysed
with the same categorizer. The adjoin/split/flatten target frames carry 95.71%,
99.90%, and 97.93% of their respective threads, so their process setup share
is under 5%. The refreshed factor target carries 58.23% of the whole thread
and is still the single dominant frame; its phase percentages below are
reported against that deliberately unfiltered denominator. Raw captures carry
no lean-bench-samply calibration/sensitivity diagnostics, which is the
declared scope of fixed-family profile coverage.

| family | case | retained / rejected | calibration residual | leaf cost | classified |
|---|---|---:|---:|---|---:|
| `tower-coordinate-arithmetic` | `runTowerMulLadder` n=12 | 4,957 / 237,605 | 0.700 ms | allocation 39.72%, Lean runtime 31.07%, GMP 23.56%, own code 4.80% | 99.15% |
| `tower-coordinate-arithmetic` | `runTowerInvLadder` n=6 | 4,943 / 2,854 | 0.542 ms | GMP 43.19%, allocation 34.86%, Lean runtime 19.97%, own code 1.60% | 99.62% |
| `trager-factorization` | `runTowerFactorLadder` degree 24 (raw fixed capture) | 16,325 / n.a. | n.a. | GMP 74.54%, Lean runtime 15.34%, allocation 9.21%, own code 0.78% | 99.87% |
| `adjoin-extend` | `runAdjoin` (raw fixed capture) | 13,786 / n.a. | n.a. | allocation 46.44%, GMP 27.26%, Lean runtime 24.05%, own code 2.01% | 99.75% |
| `split-flatten` | `runSplit` (raw fixed capture) | 9,985 / n.a. | n.a. | Lean runtime 40.01%, allocation 37.91%, GMP 13.52%, own code 7.83% | 99.27% |
| `split-flatten` | `runFlatten` (raw fixed capture) | 18,762 / n.a. | n.a. | allocation 37.74%, Lean runtime 37.06%, GMP 20.47%, own code 4.47% | 99.74% |

The two retained filtered captures pass calibration (residuals 0.54 to 0.70 ms
against the 5 ms limit), retained-sample minimums, and the ±5 ms
sensitivity check. The large rejected count on the multiplication capture is
the untimed `m = 12` tower-fixture prelude, excluded by construction.

### `tower-coordinate-arithmetic`: attributes cleanly

Multiplication at dimension 24: 100% of retained samples inside the
registered target, 99.92% in `Hex.NumberTower.mul` →
`Arithmetic.mulCoords`, splitting into `Arithmetic.convolve` (81.76%) and
the recursive top-down `Arithmetic.reduce`/`reduceCoeffs` (58.34%/56.93%,
overlapping inclusive shares). That is exactly the derivation at the
registration site: mixed-radix convolution plus reduction by each monic
defining polynomial. Inversion at dimension 12: 96.90% in
`Hex.NumberTower.inv` → `Arithmetic.invCoords`, dominated by the extended
gcd `Hex.DensePoly.xgcdLeftAux` (90.86%) whose inner work is tower
multiplication (`mulCoords` 76.37%) and polynomial division
(`DensePoly.divMod` 49.77%). Both phases named by the SPEC's arithmetic
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
(§Ordered Trager assessment).

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
kernels are HexNumberField surfaces with their own registered evidence. No
capture shows a dominant cost in a function the SPEC does not name as part
of the measured operation, and no audit-found issue was filed from these
captures.

### Artefact traceability

| artefact | source commit / role | host state | SHA-256 |
|---|---|---|---|
| [common mode-1 export](bench-results/hex-number-field-tower-phase4-mode1-nine-and-constructor-diagnostic-d277c583-chungus2-cpu19.json) | clean `d277c583b`; nine final passes plus retained constructor model discovery | [CPU-19 preflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | `9bea0ee7378b3cf8b71bccb200cdf09e92085b8806ef4d19bab704c25e92b793` |
| [corrected constructor export](bench-results/hex-number-field-tower-phase4-final-ofq-e63e3a589-chungus2-cpu19.json) | clean `e63e3a589`; final affine constructor verdict | [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | `f703055985a9b4f25b69bd954d7072f08b505896cc1625ad7ec98e102f55f65b` |
| [final mode-3 export](bench-results/hex-number-field-tower-phase4-final-mode3-d277c583-chungus2-cpu19.json) | clean `d277c583b`; six canonical budgets | [CPU-19 preflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | `dcae0daaac0470764794b793606a005a83c845dd9af44a80f61ddad97e593f06` |
| [ordered-mode diagnostics](bench-results/hex-number-field-tower-phase4-mode3-diagnostics-b2ebf281-chungus2-cpu1.json) | pre-rebase `b2ebf281b` (maps to `2a14b67a8`); temporary executable diagnostics | CPU 1 | `6f3182498feec6f8b4d7fb121f5cd67fb5b1ba011117b1e72e3431217981270d` |
| [CPU-19 preflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | measurement protocol | sampled CPU and SMT sibling | `cbb9ae6f454ed300d51e10dfb01f7454b568bde45b74e6a7b033b2b55b22c8d8` |
| [constructor postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | measurement protocol | sampled CPU and SMT sibling | `79d70f64f57983dfed82d96732510106b5ae54aabe304c309d3e90c80f366738` |
| [canonical factor profile](bench-results/hex-number-field-tower-phase4-final-factor-profile-5d4cb88a-chungus2.json) | pre-rebase binary `5d4cb88ad`; algorithm source unchanged | unpinned shape capture | `f34c803bc741a92b9ac5b6040b107aa80c206f9a8b1d6515635ca6af5d3c9cf2` |
| [factor degree diagnostic](bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json) | clean `7d6c0c50a`; rejects the former envelope | CPU 13 | `c0ae3da96fe41f36a87ed6665bf98cd1b2d4c9c209b541a7a0516cbdb28f9d30` |
| [component anchors](bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json) | clean `3f23d6425`; hash/attribution only | CPU 13 | `1927e8268c5ac22a1df0e987db5dff878e7ccdcc448252d21b6ee6240689f156` |
| [PARI pairs](bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json) | clean `322f53b15`; identical comparator sources | CPU 13 | `5c60e35f20265683fff0eb01f397e3355957fcd0737f0ca21e7781a0b30f0a3f` |
| [coordinate profile summaries](bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json) | clean `d9fc6d73f` binary | unpinned shape capture | `31767bff125621d07391e151bc613a3a1c8ee7b74300a81fd7029af2198b505c` |

The evidence added here comprises the single-root bounded-height fixtures, ten
direct mode-1 surfaces, six independently budgeted mode-3 composites, the
failed parameterizations that justify those selections, explicit retry and
recursive-relative branch exercise, and an inclusive canonical factor profile.
The component, protocol, hash, and comparator exports retain only their stated
roles. This resolves both [#9665](https://github.com/kim-em/hex-dev/issues/9665)
and the subsumed [#9815](https://github.com/kim-em/hex-dev/issues/9815).

Toolchain: Lean 4.34.0-rc2, LeanBench 0.1.0, samply 0.13.1, PARI 2.17.2,
and cypari2 2.2.4. Reference host: `chungus2`, Linux x86-64, AMD EPYC 9455
48-Core Processor, 96 logical CPUs.

## Verification

- `lake build HexNumberFieldTower HexNumberFieldTower.Conformance
  hexnumberfieldtower_emit_fixtures`: pass.
- `lake exe hexnumberfieldtower_bench list`: 10 parametric plus 38 fixed
  registrations.
- `lake exe hexnumberfieldtower_bench verify` with the cypari2 driver: all 48
  pass in 14.1 s.
- Emitted Tower fixtures match the committed JSONL byte for byte; the PARI
  oracle checks 9 cases with 0 failures.
- `python3 scripts/check_phase4.py`: pass (54 headline reports, 8 changed
  registrations).
- `python3 scripts/check_dag.py`: pass.

## Concerns

None.
