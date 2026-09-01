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
It registers seven controlled parametric targets and 37 fixed targets (44
total). The adjacent comments derive every parametric model before measurement
and document the ordered-mode assessment for each fixed performance target.

| target | operation and controlled input | declared model |
|---|---|---|
| `runTowerAddLadder` | coordinate addition in the height-two tower `ℚ(√2, 3^(1/n))` at dimension `D = 2n`, both operands dense and all-nonzero | `n` |
| `runTowerSubLadder` | coordinate subtraction on the same bounded-height family | `n` |
| `runTowerNegLadder` | coordinate negation on the same bounded-height family, including the fixed result/checksum intercept | `n + 1` |
| `runTowerSMulLadder` | scalar multiplication by the fixed rational `3/5` on the same family | `n` |
| `runTowerMulLadder` | schoolbook tower multiplication and recursive top-down reduction at dimension `D = 2n` | `n * n` |
| `runTowerInvLadder` | recursive extended-gcd inversion in the top quotient over the fixed quadratic base | `n * n * (Nat.log2 (n + 2) + 1)` |
| `runTowerDivLadder` | one recursive inversion followed by multiplication and reduction | `n * n * (Nat.log2 (n + 2) + 1)` |

The eight fixed registrations below are Phase-4 **mode 3** performance
evidence. Their ceilings are operation-specific zero-grace whole-child budgets,
not inherited harness timeouts:

| target | canonical input | budget |
|---|---|---:|
| `runOfQAdjoin` | the checked `ℚ(√2)` presentation | 0.5 s |
| `runAdjoin` | adjoin the fourth root of two to `ℚ(√2)` | 3 s |
| `runAdjoinIdentity` | re-adjoin `√2` to `ℚ(√2)` | 1 s |
| `runFactorRetry` | `X² - 3` over `ℚ(√2)`, forcing a bad first shift | 1 s |
| `runFactorRecursive` | `X² - 3` over `ℚ(√2, √3)`, forcing relative recursion | 1 s |
| `runTowerFactorLadder` | degree-24 `X^24 - X - 1` over `ℚ(√2)` | 2 s |
| `runSplit` | `(X² - 2)(X² - 3)` through two genuine extensions | 1 s |
| `runFlatten` | the dimension-four tower `ℚ(√2, √3)` | 1 s |

Modes 1 and 2 are unavailable for these cases for the reasons given at their
registration sites and in §Verdicts: their checked end-to-end phase mixtures do
not have stable independently derived one-parameter wall models, and the
published bounds available for individual factorization or isolation
algorithms do not cover the inclusive dominant executable phases. Selecting
mode 3 deliberately gives up asymptotic regression detection without changing
the SPEC's worst-case contracts.

The remaining fixed registrations make narrower claims and do not discharge
performance coverage. `runAdd`, `runSub`, `runNeg`, `runMul`, `runInv`,
`runDiv`, and `runSMul` are expected-hash anchors for operations covered by the
seven ladders. `runOneLevelNorm`, `runShiftSearch`, `runFactorRat`,
`runCheckFactorization`, `runBasisImages`, `runCertifies`,
`runCoordinateMaps`, `runRecoverPair`, and `runRecoverSearch` are correctness,
branch, and attribution anchors. The twelve `runTowerFactorPair*` /
`runPariNfFactor*` registrations are comparator endpoints, and
`runPariNfFactorOverhead` is a protocol-overhead control. Every fixed target
has an `expectedHash`; hashes, comparator agreement, and protocol timing are
not presented as performance modes.

### Fixture control

The arithmetic ladders share one prep, `prepElemInput`, which builds the
height-two tower `ℚ(√2, 3^(1/m))` (dimension `D = 2m`; `X^m - 3` is
Eisenstein-irreducible and stays irreducible over `ℚ(√2)`) and two dense
all-nonzero coordinate vectors from `ladderCoords`. As first registered,
`ladderCoords` built coordinate `i` as `±(i + salt + 2) / (i + 3)`: a
denominator varying with the coordinate index makes the lcm of the vector's
denominators grow with `Θ(D)` bit length, so the ladders varied coefficient
height together with dimension and could not test a fixed-height cost model.
This is the same defect the HexNumberField report documents for its early
fixtures, and it gets the same correction: numerators now cycle modulo 11 and
denominators modulo 6, so every reduced common denominator divides
`lcm(1, ..., 6) = 60` at every dimension and the declared `O(D)` / `O(D²)` /
`O(D² log D)` wall models see fixed-height rational operations. The
correction landed at `bc3778b79`; every number in this report postdates it.

The tower prep now certifies only the positive root of `X^m - 3`. Integer
Newton iteration supplies an untrusted Mahler-precision dyadic seed and
HexRoots' `isolateOne?` checks that the seed region contains exactly one simple
root. The former prep ran the whole-polynomial `isolate`, refined every complex
root to separation depth, proved the regions pairwise disjoint, and then kept
only the first atom. That cost bounded the ladder fixture rather than the timed
arithmetic. The local full `verify` wall time fell from about 45 s to 24.3 s
after this change even though four arithmetic ladders were added.

The Trager ladder's Selmer trinomials `X^n - X - 1` (irreducible over `ℚ`
for every `n ≥ 2`, and over `ℚ(√2)` because their Galois group leaves the
root field without quadratic subfields) have rational coefficients, so the
shift-zero one-level norm is the square `f²` and the bounded shift search
always performs a genuine retry before accepting a squarefree norm. The same
coefficient array feeds the PARI comparator requests, so both sides factor
the identical input. Every fixture in this library is deterministic; no
registration draws from a random seed.

### Scientific ranges

Addition, subtraction, negation, scalar multiplication, inversion, and
division run at `n = 1, 2, 3, 4, 6` (dimension 2 through 12), the range the
library's merge-facing conformance bound (tower dimension at most 8, plus the
dimension-12 asymptotic rung) makes meaningful.
The multiplication schedule extends through `n = 8, 12` because its
normalized cost has a small-dimension transient (per-element construction and
the `O(D)` checksum walk weigh more against `D²` work at dimension four) that
flattens from `n = 6` on; the short schedule ended inside the transient and
produced a spurious `+0.17` residual against the quadratic model. The raised
per-call cap accommodates the untimed tower construction at `m = 8` and
`m = 12` in prep (its `adjoin?` factors `X^m - 3` over `ℚ(√2)` outside the
timed region).

All seven parametric registrations set `signalFloorMultiplier := 1.0`. The
justification tracks `SPEC/benchmarking.md` §Spawn-floor filter: every rung
uses warm child-side inner repeats auto-tuned to a 100 ms timed batch, and five
fresh outer trials supply a robust median. Process spawn is outside that timed
body, so the conservative default 10x multiplier would discard submicrosecond
operations without changing what is measured. JSON exports record
`spawn_floor_nanos` and every individual trial.

### Fixed-case timing discipline

A fixed repeat is one fresh child process, so a registration whose body reads
a lazily cached `IO.Ref` fixture initially paid the fixture construction
inside its first (and, at `inner_repeats = 1`, only) timed call: the
coordinate arithmetic cases reported ~17 ms medians that were the two-level
tower construction, not the `D = 4` coordinate operation, and the flattening
component cases similarly reported their candidate-search fixtures. The
repair (`3f23d6425`) adopts the shape the PARI pairs already documented:
`warmupFirstIter` performs one discarded call that populates the
process-local cache outside the timed region, and `minTotalSeconds := 0.2`
amortises steady-state work across the auto-tuned inner-repeat batch. All
fixed medians below postdate the repair.

### Smoke cost

A full `.lake/build/bin/hexnumberfieldtower_bench verify` of all 44
registrations, with `HEX_PARI_BENCH_PYTHON` pointed at the cypari2 environment,
passes locally in 24.3 s against CI's repo-wide hard cap and under the 30 s
per-library soft warning. The cost remains dominated by `runRecoverSearch`;
the single-root fixture removes the all-roots separation prelude from every
arithmetic ladder.

## Verdicts

The definitive arithmetic and mode-3 exports were taken on the shared
`chungus2` host after `scripts/bench/idle_core.py` identified an idle logical
CPU and its SMT sibling. The selected CPU, host load, spawn floor, and every
trial are recorded in the exports.

```sh
taskset -c 3 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerAddLadder \
  Hex.NumberTowerBench.runTowerSubLadder \
  Hex.NumberTowerBench.runTowerSMulLadder \
  Hex.NumberTowerBench.runTowerMulLadder \
  Hex.NumberTowerBench.runTowerInvLadder \
  Hex.NumberTowerBench.runTowerDivLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-final-arithmetic-six-8f031f1e-chungus2-cpu3.json
taskset -c 1 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerNegLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-final-neg-affine-a047adfc-chungus2-cpu1.json
taskset -c 3 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runOfQAdjoin \
  Hex.NumberTowerBench.runAdjoin \
  Hex.NumberTowerBench.runAdjoinIdentity \
  Hex.NumberTowerBench.runFactorRetry \
  Hex.NumberTowerBench.runFactorRecursive \
  Hex.NumberTowerBench.runTowerFactorLadder \
  Hex.NumberTowerBench.runSplit \
  Hex.NumberTowerBench.runFlatten \
  --repeats 5 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-final-mode3-5d4cb88a-chungus2-cpu3.json
```

All seven arithmetic registrations select **mode 1, two-sided parametric**.
Their independently derived family models are in §Bench targets and at the
registration sites. The definitive results are:

| target | ladder | verdict | fitted slope | worst spread |
|---|---|---|---:|---:|
| `runTowerAddLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.095 | 65.1% |
| `runTowerSubLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.105 | 67.7% |
| `runTowerNegLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.094 | 5.9% |
| `runTowerSMulLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.080 | 36.7% |
| `runTowerMulLadder` | 1, 2, 3, 4, 6, 8, 12 | **consistent** | +0.074 | 99.2% |
| `runTowerInvLadder` | 1, 2, 3, 4, 6 | **consistent** | −0.023 | 2.5% |
| `runTowerDivLadder` | 1, 2, 3, 4, 6 | **consistent** | +0.249 | 8.8% |

All result hashes agree at every rung and trial. The large worst-spread entries
come from isolated slow trials (including one doubled multiplication trial at
`n = 12`); the five-trial medians and fitted slopes remain stable, which is
why the export retains every trial rather than selecting a minimum.

The mode-3 export supplies the enforced absolute-budget verdicts:

| target | median | budget | hash |
|---|---:|---:|---|
| `runOfQAdjoin` | 0.518 µs | 0.5 s | match |
| `runAdjoin` | 310.047 ms | 3 s | match |
| `runAdjoinIdentity` | 18.191 ms | 1 s | match |
| `runFactorRetry` | 0.819 ms | 1 s | match |
| `runFactorRecursive` | 7.574 ms | 1 s | match |
| `runTowerFactorLadder` | 250.897 ms | 2 s | match |
| `runSplit` | 67.971 ms | 1 s | match |
| `runFlatten` | 20.946 ms | 1 s | match |

Every repeat completed under its declared whole-child ceiling and matched its
`expectedHash`. The harness's submicrosecond advisory on `runOfQAdjoin` is
expected here: the input is read through runtime `IO.Ref` state, while the
operation itself is a fixed-size dependent presentation constructor rather
than an isolation or factorization call. `runFactorRetry` computes the
repeated shift-zero norm before
accepting a later squarefree norm. `runFactorRecursive` factors through the
intermediate `ℚ(√3)` level rather than taking an invalid absolute-norm
shortcut. The degree-24 canonical case performs the same real retry, recursive
rational factorization of the accepted degree-48 norm, gcd recovery, and
checked replay end to end.

### Ordered Trager assessment

The archived degree sweep `2, 3, 4, 6, 8, 12, 16, 24` remains diagnostic
evidence for rejecting stronger modes. Against the former Trager/BHKS envelope
it was inconclusive and faster by `n^6.506`; its successive local exponents
rose from 0.80 to 4.48 as coefficient-growth phases took over. There is no
stable independently derived family-specific model for that changing phase
mixture, so mode 1 is unavailable. Mode 2 is also unavailable: the original
filtered profile assigned only 5.26% to `Hex.ZPoly.factorize`, and the
refreshed canonical degree-24 profile assigns only 1.42%, while
rational-polynomial gcd, checked replay, shift search, and resultant work
dominate. The BHKS bound covers only that small integer-factorization phase.
The mode-3 canonical input is the sweep's top completed rung, and its 2 s
ceiling is a measured-baseline-plus-margin budget, not a reinterpretation of
the failed envelope.

The 16 fixed anchors named in §Bench targets retain the clean
`3f23d6425` component export for hash and attribution evidence. They are not
assigned modes and none is counted as advertised-operation performance
coverage.

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
(§Verdicts).

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

| artefact | source commit | host state | SHA-256 |
|---|---|---|---|
| [`bench-results/hex-number-field-tower-phase4-final-arithmetic-six-8f031f1e-chungus2-cpu3.json`](bench-results/hex-number-field-tower-phase4-final-arithmetic-six-8f031f1e-chungus2-cpu3.json) | pre-rebase `8f031f1eb`; bench source byte-identical to `13a85dba4` | idle, CPU 3 | `b979fccfb99f621f66876dd0042b3f8d3dbe7d62496da438244311ed0e3f178e` |
| [`bench-results/hex-number-field-tower-phase4-final-neg-affine-a047adfc-chungus2-cpu1.json`](bench-results/hex-number-field-tower-phase4-final-neg-affine-a047adfc-chungus2-cpu1.json) | pre-rebase `a047adfc5`; bench source byte-identical to `fb4752260` | idle, CPU 1 | `9a075d7d6ab99f2f354a197dae215aba70a36f967e320c9f757c3669bba04f35` |
| [`bench-results/hex-number-field-tower-phase4-final-mode3-5d4cb88a-chungus2-cpu3.json`](bench-results/hex-number-field-tower-phase4-final-mode3-5d4cb88a-chungus2-cpu3.json) | pre-rebase `5d4cb88ad`; bench source byte-identical to `7ad34c201` | idle, CPU 3 | `b2464e7a764c38beabea941c08fa83997292039abdc71d6646eb23750d45cf56` |
| [`bench-results/hex-number-field-tower-phase4-final-factor-profile-5d4cb88a-chungus2.json`](bench-results/hex-number-field-tower-phase4-final-factor-profile-5d4cb88a-chungus2.json) | pre-rebase binary `5d4cb88ad`; source matches `7ad34c201` | unpinned (shape capture) | `f34c803bc741a92b9ac5b6040b107aa80c206f9a8b1d6515635ca6af5d3c9cf2` |
| [`bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json) | clean `7d6c0c50a` | idle, CPU 13 | `c0ae3da96fe41f36a87ed6665bf98cd1b2d4c9c209b541a7a0516cbdb28f9d30` |
| [`bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json) | clean `3f23d6425` | idle, CPU 13 | `1927e8268c5ac22a1df0e987db5dff878e7ccdcc448252d21b6ee6240689f156` |
| [`bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json) | clean `322f53b15` (identical bench sources to `3f23d6425`) | idle, CPU 13 | `5c60e35f20265683fff0eb01f397e3355957fcd0737f0ca21e7781a0b30f0a3f` |
| [`bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json`](bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json) | binary from clean `d9fc6d73f` | unpinned (shape capture) | `31767bff125621d07391e151bc613a3a1c8ee7b74300a81fd7029af2198b505c` |

The current evidence adds the single-root arithmetic fixture, four missing
arithmetic ladders, eight explicit mode-3 budgets, and the canonical degree-24
profile. The older degree sweep remains only as the evidence for rejecting
modes 1 and 2, while the component and comparator exports retain their stated
hash, attribution, and informational roles. Toolchain throughout: Lean
4.34.0-rc2 (`leanprover/lean4:v4.34.0-rc2`), LeanBench 0.1.0, samply 0.13.1,
PARI 2.17.2 driven by cypari2 2.2.4 through
`scripts/oracle/pari_bench_driver.py` (Python from `HEX_PARI_BENCH_PYTHON`).
Host throughout: `chungus2`, Linux x86-64 6.12.100, AMD EPYC 9455 48-Core
Processor, 96 logical CPUs; each timing row states its selected idle CPU.

## Concerns

None.
