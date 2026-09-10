# HexNumberFieldTower Performance Report

`HexNumberFieldTower` is a compiled-track library: every operation it
advertises is Mathlib-free executable computation, so all of its Phase-4
evidence is ordinary LeanBench evidence and none of it is fresh-module proof
evidence (`PLAN/Phase4.md` §Evidence tracks). This snapshot records that
evidence as measured on the reference host; `libraries.yml` records the
library's phase. Every advertised operation has an admissible ordered mode:
eight parametric registrations pass their source-derived models and nine
canonical cases carry zero-grace mode-3 ceilings.

## Bench targets

The compiled Mathlib-free driver is `bench/HexNumberFieldTower/Bench.lean`.
It registers eight controlled parametric targets and 41 fixed targets (49 total).
Eight parametric models supply admissible mode-1 evidence, including recursive
inversion on the normalized monic extended-gcd chain. Nine surfaces have
independently justified mode-3 registrations: the seven composite surfaces
below, division at the top rung of the recursive family, and the dense
single-call `toPrimitive` map.

| target | controlled timed operation | mode-1 model |
|---|---|---|
| `runOfQAdjoinLadder` | checked rational presentation construction at degree `n` | `n` |
| `runTowerAddLadder`, `runTowerSubLadder`, `runTowerSMulLadder` | coordinatewise work in `ℚ(√2, 3^(1/n))`, dimension `D = 2n` | `n` |
| `runTowerNegLadder` | one public negation and structural result hash over `D = n` dense coordinates | `n` |
| `runTowerMulLadder` | schoolbook convolution and recursive reduction | `n²` |
| `runTowerInvLadder` | recursive inversion in `ℚ(3^(1/n), √2)`: the monic top-level extended gcd whose coefficient work recurses into the degree-`n` lower field | `n² log n` |
| `runFromPrimitiveLadder` | apply `fromPrimitive` to all `D` primitive basis vectors | `n⁴` |

One `fromPrimitive` Horner evaluation performs `D` tower operations of
`Θ(D²)` each, hence `Θ(D³)` per vector and `Θ(D⁴)` for the full basis. A dense
`toPrimitive` call has an `O(D²)` rational-operation bound, but its bit cost is
set by the flattening's primitive-basis images rather than by the prepared
input, so it is a mode-3 surface below. Recursive inversion's `n² log n` model
is the `Θ(n²)` coordinate work of the constant number of lower-field inversions
and products that the monic top-level chain performs, with the logarithmic
factor as the limb-growth proxy; the untimed `tower-inv-chain-stats` replay
records that count and the operand heights at every rung.

The following nine registrations are mode-3 performance evidence.
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
| `runTowerDivRecursive` | divide two dense bounded-height elements of `ℚ(3^(1/12), √2)`, dimension 24 | 3 s |
| `runToPrimitiveDense` | one dense `toPrimitive` call on the flattening of `ℚ(√2, 3^(1/5))`, dimension 10 | 10 s |

All other fixed registrations are deliberately narrower evidence.
`runOfQAdjoin`, `runToPrimitive`, and the fixed arithmetic cases are
expected-hash anchors; in particular, the cheap dimension-four `runNeg` and
`runDiv` cases do not replace the negation ladder or the canonical division case.
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
to recurse into the degree-`n` lower field. That top-level gcd is the monic
chain `DensePoly.xgcdLeftMonic`: every remainder is normalized before it
divides, so each recursive lower-field inversion acts on a bounded operand.
Dense coordinate numerators cycle modulo 11 and
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
recursively factors it over `ℚ`, returns the canonical component through
singleton recovery, and checks the result. Thus the eight Hex cases in this
comparison all use a quadratic top level and a singleton norm factor; their
speedups do not measure the multiple-factor gcd recovery branch. Reducible
conformance and differential cases cover that branch for correctness. The
explicit retry anchor and independently budgeted height-two recursive case
confirm both control-flow paths.

### Scientific ranges and host protocol

Coordinatewise add/subtract/scalar multiplication use `n = 1, 2, 3, 4, 6`;
multiplication extends through `8, 12`. Negation uses dimensions
`128, 160, 192, 256, 320, 384, 448`, and the recursive inversion family uses
`2, 3, 4, 6, 8, 12`.
Presentation construction uses `2, 3, 4, 6, 8, 12, 16, 24`, and the
full-basis `fromPrimitive` closure uses
`2, 3, 4, 5, 6, 9`. Every parametric rung except negation uses a warm
child-side batch auto-tuned to 100 ms and five
independent outer trials. Negation uses a five-second target and trial-major
interleaving across its seven dimensions. The explicit
`signalFloorMultiplier := 1.0` is appropriate because process spawn is
outside the timed body; the exports retain the spawn floor and every trial.
LeanBench drops the first of the seven ordered rungs from its slope fit, so the
reported residual is fitted over dimensions 160 through 448; dimension 128 is
retained as a measured allocation-regime and normalized-cost check.

The original final exports were pinned to logical CPU 19, with SMT sibling 67.
Immediately before the dense `toPrimitive` export, `scripts/bench/idle_core.py`
certified logical CPU 16 and its SMT sibling 64 idle; the run was pinned to CPU
16 and records clean pre-rebase commit `85f9c303f` (now `27033e761`). For the
original CPU 19 protocol, a
three-second `/proc/stat`
postflight sample measured 1.33% busy on each sibling; load averages were 1.28,
2.53, and 2.87 on a 96-logical-CPU host. This is a postflight protocol check,
not a claim that the host was idle throughout.

The negation export used logical CPU 3 with SMT sibling 51. A continuous
250 ms `/proc/stat`/runnable-process trace was intersected with LeanBench's 481
timed-loop regions from 35 PID-specific sidecars. It retained 136.213 seconds
of timed work, found no foreign runnable sample on CPU 3, and measured 0.257223
seconds of sibling activity: aggregate ratio 0.001888, below the pre-registered
0.002 ceiling. The diagnostic's numerator is precisely sampled sibling busy
time plus the whole timed overlap of any sample in which a foreign runnable
process (any task in the current schema) is observed on the measurement CPU.
It is deliberately conservative, but is not
the process-CPU residual used by `fresh_module_sweep.py`; the shared numeric
ceiling does not make those two diagnostics interchangeable.
The committed schema-1 trace sampled process leaders; the current monitor now
checks every `/proc/<pid>/task/<tid>/stat` worker thread and excludes Linux
guest-time double counting. For the accepted historical trace, the raw CPU-3
counters cover 136.067 of the 136.213 timed seconds, corroborating that almost
the entire measurement-core capacity was occupied by the pinned benchmark;
this corroboration is not represented as a stronger per-process attribution.

The run series used a finite one-retry bound. The first attempt at the same
committed implementation and schedule was rejected at 0.003274; its timing
export and telemetry are retained below. After an idle-core preflight, the one
unchanged retry supplied the official export above. No further retry would
have been admitted.

```sh
taskset -c 19 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runOfQAdjoinLadder \
  Hex.NumberTowerBench.runTowerAddLadder \
  Hex.NumberTowerBench.runTowerSubLadder \
  Hex.NumberTowerBench.runTowerSMulLadder \
  Hex.NumberTowerBench.runTowerMulLadder \
  Hex.NumberTowerBench.runFromPrimitiveLadder \
  --outer-trials 5 --export-file <mode1.json>

taskset -c 16 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerInvLadder \
  Hex.NumberTowerBench.runTowerDivLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-recursive-arithmetic-800bd23da-chungus2-cpu16.json

taskset -c 3 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerDivRecursive \
  Hex.NumberTowerBench.runToPrimitiveDense \
  --export-file reports/bench-results/hex-number-field-tower-mode3-division-dense-map-900e3aad8-chungus2-cpu3.json

.lake/build/bin/hexnumberfieldtower_bench tower-inv-chain-stats \
  > reports/bench-results/hex-number-field-tower-inv-chain.csv
.lake/build/bin/hexnumberfieldtower_bench tower-div-chain-stats \
  > reports/bench-results/hex-number-field-tower-div-chain.csv
.lake/build/bin/hexnumberfieldtower_bench tower-to-primitive-stats \
  > reports/bench-results/hex-number-field-tower-to-primitive-images.csv

taskset -c 16 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runToPrimitiveLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-dense-to-primitive-85f9c303-chungus2-cpu16.json

python3 scripts/bench/core_telemetry.py --cpu 3 \
  --output <negation-telemetry.json> --interval 0.25 \
  --max-core-interference-ratio 0.002 --fail-on-contamination -- \
  .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerNegLadder --outer-trials 5 \
  --export-file <negation-mode1.json>

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
| `runTowerNegLadder` | 128, 160, 192, 256, 320, 384, 448 | **consistent** | +0.038 | 14.229–15.239 | 11.42% | negation mode-1 |
| `runTowerMulLadder` | 1, 2, 3, 4, 6, 8, 12 | **consistent** | +0.096 | 3,866.98–4,394.58 | 3.96% | original mode-1 |
| `runFromPrimitiveLadder` | 2, 3, 4, 5, 6, 9 | **consistent** | −0.026 | 8,393.62–8,775.98 | 11.89% | original mode-1 |
| `runTowerInvLadder` | 2, 3, 4, 6, 8, 12 | **consistent** | −0.010 | 9,048.37–12,199.10 | 1.96% | repaired inversion mode-1 |

All eight rows use their source-derived models with LeanBench's default
slope tolerance. No intercept was added and no tolerance was widened after
measurement. The inversion row is the repaired monic chain measured on five
independent trials at clean commit `800bd23da`; before the repair the same
registration, family and schedule gave β = +0.522, retained in the pre-repair
diagnostic export. The dense `toPrimitive` ladder that this table used to
carry (β = +0.996 and +1.023 on two clean runs) is no longer a registration;
its exports remain the recorded diagnostic behind the mode-3 case below.

### Ordered-mode assessment

Before selecting absolute budgets, executable diagnostics attempted the
natural degree/factor-count parameter for every composite surface:

Negation is not in the table below. The implementation maps
`Rat.neg` over all `D` coordinates, wraps the proof-known exact-width array
without normalizing or copying it, then hashes all `D` result coordinates. The
schedule begins above the 1,024-byte mimalloc fast-small boundary at D=125 and
ends below the 4,096-byte small-object boundary at D=509, so every rung uses
the same source-derived allocation route. A temporary `IO.getNumHeartbeats`
diagnostic measured stable counter deltas D+3 (131 at D=128 and 259 at D=256),
with a one-allocation measurement baseline, confirming D+2 operation
allocations and no sharing or short circuit. The repeated counts and empty-body
control are retained below rather than only described from a temporary probe.

There were two distinct failures before the accepted run. The original small
schedule (dimensions 4 through 48) produced β = −0.162 and motivated the
source-based allocation-threshold audit. The preregistered seven-rung schedule
then produced β = +0.414 with the old normalizing reconstruction and a 100 ms
inner target. That result did not justify changing the model or schedule: the
inclusive profile exposed the extra reconstruction traversal, the public
implementation was repaired to use the proof-known exact width, and the
five-second target was committed to amortize allocator-page maintenance. Only
then was the official export collected.

| surface | attempted schedule and observed result | ordered-rule conclusion |
|---|---|---|
| inversion | the checked height-two family `ℚ(3^(1/n), √2)` gave β = +0.522 against `n² log n` while the top-level chain was the unnormalized `xgcdLeft`; the untimed replay attributes the excess to repeated lower-field inversions on height-amplified operands | implementation defect, repaired: the chain now normalizes every remainder (`xgcdLeftMonic`), every value and hash is unchanged, and the unchanged preregistered model passes at β = −0.010: mode 1 |
| division | the same family gave β = +0.748 (and +0.594 in the opposite tower order) before the repair and β = +0.191 after it; the replay charges the product by the inverse at 9% to 20% of the limb work, and the inverse's coordinate height crosses from two to three 64-bit limbs between `n = 8` and `n = 12` (123 and 211 bits) | inversion is the dominant phase and carries the parametric evidence; no one-parameter wall model tracks the limb step on this range: mode 3 at the top completed rung |
| dense `toPrimitive` | one prepared all-nonzero input at each `D = 2n` rung rejects the preregistered quadratic model with β = +0.996 and +1.023; the untimed image replay records primitive-image heights of 4, 12, 11, 33, 25 and 112 numerator bits on the schedule, set by the accepted primitive-element shift and not monotone in `n` | `QAdjoin.add` and `QAdjoin.smul` perform the expected `Θ(D²)` rational operations on an input-determined height, so no wall model in `n` alone is reachable: mode 3 at the tallest-image rung whose fixture is affordable |
| adjoin | degrees 2, 3, 4, 6, 8: 13.7 ms, 35.5 ms, 98.1 ms, 804.5 ms, 4.71 s; degree 12 hit 30 s | isolation, factor selection, and validation change dominance |
| identity adjoin | degrees 2, 3, 4: 18.0 ms, 2.37 s, 1.68 s; degree 6 hit 30 s | branch-sensitive recovery is nonmonotone |
| recursive relative factorization | Selmer degrees 2, 3, 4, 6 over a height-two tower take 7.598, 12.320, 18.591, and 46.578 ms, giving β = +0.636 against the attempted linear model | the recursive level changes the gcd/resultant/replay mixture |
| checked replay | degrees 2 through 24: 0.404 ms through 126.3 ms; linear residual +1.485 | squarefree, gcd, and replay work do not admit the candidate wall model |
| factor | degrees 2 through 24; local exponents rise 0.80 to 4.48 | gcd/resultant/replay shares change with coefficient growth |
| split | factor-count 1 is excluded from the verdict; the eligible 2-to-3 jump is 68.3 ms to 1.89 s (27.7×) | repeated factor/isolate/adjoin phases change dominance |
| flatten | top degrees 1, 2, 3, 4: 0.96 ms, 21.0 ms, 107.7 ms, 460.4 ms | eliminant/isolation/recovery phases change dominance |

The diagnostics are retained executable measurements, not informal timing
notes. The first row is mode 1 after its implementation repair. The next two
rows and the seven composite surfaces have no tight independently justified
mode-1 model and no published bound covering their inclusive dominant phases;
their canonical mode-3 budgets are therefore the next ordered choice.

| target | per-call median | median auto-tuned batch | ceiling | result |
|---|---:|---:|---:|---|
| `runAdjoin` | 311.405 ms | 311.405 ms | 3 s | hash match, under ceiling |
| `runAdjoinIdentity` | 18.084 ms | 289.345 ms | 1 s | hash match, under ceiling |
| `runFactorRecursive` | 7.919 ms | 253.393 ms | 2 s | hash match, under ceiling |
| `runTowerCheckFactorization` | 124.730 ms | 249.460 ms | 2 s | hash match, under ceiling |
| `runTowerFactorLadder` | 249.758 ms | 249.758 ms | 2 s | hash match, under ceiling |
| `runSplit` | 68.203 ms | 272.813 ms | 1 s | hash match, under ceiling |
| `runFlatten` | 20.819 ms | 333.110 ms | 1 s | hash match, under ceiling |
| `runTowerDivRecursive` | 8.737 ms | 279.575 ms | 3 s | hash match, under ceiling |
| `runToPrimitiveDense` | 45.139 µs | 739.567 ms | 10 s | hash match, under ceiling |

These nine ceilings were chosen from the completed diagnostic schedule and the
canonical input before the official export (five repeats for the seven composite cases, three for the two arithmetic cases, whose fixtures cost about 0.3 s and 1.8 s inside each child); the export directly
checks the inclusive whole-child ceilings with zero grace. The ceiling applies
to the whole child, while the batch column shows the actual auto-tuned work
performed in each measured repeat; the small per-call medians are not presented
as the available budget headroom. In table order the whole-child ceiling to
measured-batch margins are 9.63×, 3.46×, 7.89×, 8.02×, 8.01×, 3.67×,
3.00×, 10.73×, and 13.52×. The in-process `verify` command checks benchmark bodies and hashes,
not these process-level deadlines; the inclusive ceilings are enforced by the
recorded `run` export protocol.

### Contended-host refresh of the mode-3 cases

The nine mode-3 medians above were exported before the Trager work of #10077,
#10085 and #10110 landed. `chungus2` has no quiet window available, so a
refresh at main `b2f90bc4` uses repetition instead of quiescence: fourteen
attempts of the same registered command, each pinning to a freshly chosen
`idle_core.py` core, each retaining its own load, SMT-sibling busy fraction
measured across the run, and postflight busy on the pinned core and its
sibling. All fourteen attempts and their contexts are retained in
[the ledger](bench-results/hex-number-field-tower-mode3-refresh-attempts.json);
attempts 1, 8, 9, 11 and 12 exceed the 5% sibling or 8% postflight thresholds
and are excluded. Attempt 13 supplies the
[committed export](bench-results/hex-number-field-tower-mode3-refresh-b2f90bc4-chungus2-cpu14.json)
and its
[division/dense companion](bench-results/hex-number-field-tower-mode3-refresh-divdense-b2f90bc4-chungus2-cpu14.json).

The argument this protocol rests on is that contention inflates a timing and
never deflates it, so the minimum across attempts bounds the uncontended cost
from above. Across the nine admitted attempts every target's spread is at most
4.1%, and every observed hash agrees with the registered expectation. This is
a shared-host refresh of recorded medians, not a release-quality verdict, and
it changes no registered ceiling or complexity claim.

| target | recorded median | refreshed median | change |
|---|---:|---:|---|
| `runAdjoin` | 311.405 ms | 313.072 ms | unchanged |
| `runAdjoinIdentity` | 18.084 ms | 17.760 ms | unchanged |
| `runFactorRecursive` | 7.919 ms | 5.163 ms | 1.53× faster |
| `runTowerCheckFactorization` | 124.730 ms | 4.163 ms | 30.0× faster |
| `runTowerFactorLadder` | 249.758 ms | 9.102 ms | 27.4× faster |
| `runSplit` | 68.203 ms | 59.770 ms | 1.14× faster |
| `runFlatten` | 20.819 ms | 20.873 ms | unchanged |
| `runTowerDivRecursive` | 8.737 ms | 8.742 ms | unchanged |
| `runToPrimitiveDense` | 45.139 µs | 46.000 µs | unchanged |

`runTowerFactorLadder` at 9.102 ms independently reproduces the 9.129–9.212 ms
that #10110's own preregistered paired protocol admitted, which is the main
reason to trust the rest of the column. The two composite surfaces that moved
without being the direct target of that work, `runFactorRecursive` and
`runSplit`, both factor over quadratic towers and so run through the reduced
quadratic norm path.

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

### Rational squarefreeness in Trager

The rational base now tests the integer primitive part modulo the certified
prime 499 before running an exact rational gcd. A successful modular test is
sufficient for squarefreeness; a bad leading coefficient or discriminant falls
back to the exact test. The compiler replacement `ZPoly.ratSquarefree_eq_fast`
is kernel-proved equal to the original rational gcd predicate, including zero
and rational denominators. The tower correspondence proof transports the base
case from singleton coordinate arrays to `Rat`. Factor reconstruction,
canonical ordering, multiplicities, and recursive irreducibility replay remain
fully checked.

The [untimed remainder-sequence replay](bench-results/hex-number-field-tower-factor-heights-b4a02beaf.csv)
identifies coefficient growth inside the squarefreeness gcd, rather than a
large shift count. Every registered Selmer rung rejects shift zero and accepts
shift one; the latter is certified modulo 499. The accepted norms have integer
coefficients, but the unnormalized exact gcd creates large rational scalars:

| input degree | norm degree | norm numerator bits | gcd numerator bits | gcd denominator bits |
|---:|---:|---:|---:|---:|
| 2 | 4 | 3 | 8 | 5 |
| 3 | 6 | 4 | 46 | 42 |
| 4 | 8 | 6 | 121 | 109 |
| 6 | 12 | 9 | 449 | 438 |
| 8 | 16 | 11 | 1,035 | 1,014 |
| 12 | 24 | 17 | 3,464 | 3,430 |
| 24 | 48 | 36 | 25,546 | 25,476 |

These are maximum bit lengths over the exact remainder sequence, not fitted
costs or timing exponents. Regenerate them with
`lake exe hexnumberfieldtower_bench tower-factor-stats`. The successful modular
trial removes this rational gcd from both norm acceptance and the rational
factorizer, including their certificate replay. Rejected trials still use the
exact algorithm, so this does not improve the worst-case contract. The fixture
already has one quadratic level; no absolute-presentation conversion is needed
for this change, and deeper-tower presentation tradeoffs remain unmeasured.

The rational factorizer still recomputes the primitive part after the
squarefreeness check, and integer factorization performs its own normalization
and modular trial. This adds duplicate preprocessing work.
The captured rational-squarefreeness path is only 2.05% inclusive, so eliminating
that duplication is not needed to remove the dominant exact-gcd coefficient
growth.

### Norm construction and gcd recovery

Independent fixed-case comparisons retain two additional changes. The shifted
bivariate norm input uses a descending Horner fold, avoiding the separate
ascending-power accumulator. Recovery uses the public remainder-only division
worker with identity leading-coefficient scaling when the shifted component is
monic and smaller than its lifted norm factor. Its companion theorem proves
exact equality with the reference gcd, including the unnormalised remainder
representative and remaining fuel. All public reconstruction, irreducibility,
ordering, multiplicity, and certificate checks remain in place.


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

### Modular squarefreeness comparison

The [comparison protocol](hex-number-field-tower-factor-protocol.md) retains
the existing fixed inputs, five repeats, a 0.2-second inner-batch floor, and
unchanged 2-second canonical budgets. Two accepted paired comparisons of the
original executable against the merged modular-check executable give the
following **ranges of paired medians and speedups**. Both arms of each pair
used the same core; the second pair reversed the arm order. No exponent was
fitted. Every Hex result hash matches, including the canonical certificate
checksum, and every fresh PARI degree/multiplicity checksum matches Hex.

| operation | baseline median ms | modular median ms | paired speedup |
|---|---:|---:|---:|
| factor, degree 2 | 1.079–1.080 | 1.035–1.045 | 1.03–1.04× |
| factor, degree 3 | 1.462–1.469 | 1.393–1.407 | 1.04–1.05× |
| factor, degree 4 | 2.069–2.076 | 1.934–1.935 | 1.07× |
| factor, degree 6 | 3.597–3.600 | 3.055–3.121 | 1.15–1.18× |
| factor, degree 8 | 6.128–6.153 | 4.509–4.577 | 1.34–1.36× |
| factor, degree 12 | 16.565–16.594 | 9.262–9.298 | 1.78–1.79× |
| factor, degree 24 | 250.279–252.941 | 34.380–34.625 | 7.23–7.36× |
| check, degree 24 | 125.002–125.079 | 16.848–16.988 | 7.36–7.42× |

The accepted pairs used CPU 5/sibling 53 and CPU 15/sibling 63. Each arm
passed the registered two-second pre/post idleness checks and the mean
sibling-utilization gate during execution. The first five attempts were
rejected on host telemetry (one before timing); every rejected export is
retained alongside the accepted exports in the
[artifact manifest](bench-results/hex-number-field-tower-followup-manifest.json).
The manifest also preserves the orchestration script. Harness exports record
the measurement checkout; the host records identify each saved executable's
source commit and SHA-256. This is local shared-host evidence, not a
release-quality verdict or a replacement for Phase-4 model coverage.

Fresh PARI measurements remain informational and variable: in the two modular
arms, degree-12 medians were 76.277 and 97.002 µs, giving raw PARI/Hex time
ratios of 0.00820 and 0.01047. The corresponding protocol-overhead medians were
7.585 and 7.382 µs. These pairs establish the Hex before/after improvement;
the comparator still has a substantial gap and performs no certificate replay.

The earlier comparison series supplied no accepted result: its first
candidate's CPU/sibling were 96%/97% busy at postflight, and both
protocol-amended retries failed the 5% idleness threshold. The next baseline's
CPU/sibling were 98.5%/97.5%; the final baseline on CPU 1 failed at
13.1%/1.5%. Those retries stopped before running the candidate and remain
contaminated diagnostics, excluded from the table above.

For transparency, the first attempt's raw per-call medians are retained below
as **contaminated diagnostics only**. All repeat hashes agree, all eight Hex
before/after hashes match, and all six fresh PARI degree/multiplicity hashes
match Hex. PARI 2.17.3/cypari2 2.2.4 was available, but its timings and 10.753 µs
protocol-overhead median share the rejected run and supply no new comparator
ratio.

| operation | baseline ms | candidate ms (contaminated) |
|---|---:|---:|
| factor, degree 2 | 1.072 | 1.056 |
| factor, degree 3 | 1.462 | 1.398 |
| factor, degree 4 | 2.072 | 1.913 |
| factor, degree 6 | 3.593 | 3.099 |
| factor, degree 8 | 6.299 | 4.578 |
| factor, degree 12 | 16.978 | 9.201 |
| factor, degree 24 | 253.152 | 34.443 |
| check, degree 24 | 125.242 | 16.711 |


### Norm and recovery comparisons


The [artifact manifest](bench-results/hex-number-field-tower-followup-manifest.json)
contains complete exports and telemetry for two accepted opposite-order pairs
per variant. The eight Hex hashes match throughout. Both isolated variants
and their combination meet the registered retention criteria. These are
ranges of paired speedups on the unchanged canonical degree-24 inputs:

| variant against modular-check baseline | factor speedup | replay speedup |
|---|---:|---:|
| Horner norm construction | 1.018× | 1.019–1.022× |
| monic first recovery remainder | 1.025–1.044× | 1.004–1.019× |
| both changes | 1.017–1.032× | 1.025–1.033× |

The smaller effects are variable across local pairs and are not additive.
The 0.36% isolated recovery replay improvement in one pair is smaller than
its repeat spread: baseline min/median/max 16.626/16.819/17.068 ms and
candidate 16.466/16.759/17.085 ms. The retention rule requires both canonical
medians to improve but excludes smaller-rung regressions only when ranges
are disjoint; it is a selection rule, not a statistical significance test.
No minimum effect size was registered, and none is inferred afterward.
One isolated recovery degree-4 median increased by 0.53%; its repeat ranges
overlap, so it is not a repeat-range-disjoint regression. The combined
implementation improves every Hex median in both accepted pairs.

A separate direct comparison of the combined implementation (`8d54c7158`)
against the original executable gives the following ranges. These speedups
are measured directly, not multiplied from the ablations:

| operation | original median ms | combined median ms | paired speedup |
|---|---:|---:|---:|
| factor, degree 2 | 1.073–1.074 | 0.955–0.966 | 1.11–1.13× |
| factor, degree 3 | 1.453–1.464 | 1.271–1.275 | 1.14–1.15× |
| factor, degree 4 | 2.077–2.080 | 1.761–1.765 | 1.18× |
| factor, degree 6 | 3.573–3.587 | 2.849–2.857 | 1.25–1.26× |
| factor, degree 8 | 6.098–6.121 | 4.285–4.297 | 1.42–1.43× |
| factor, degree 12 | 16.297–16.399 | 8.695–8.767 | 1.87× |
| factor, degree 24 | 250.251–250.794 | 33.329–33.403 | 7.49–7.52× |
| check, degree 24 | 124.527–124.651 | 16.295–16.538 | 7.54–7.64× |


Fresh PARI 2.17.3/cypari2 2.2.4 measurements paired with the combined binary
remain informational. Protocol-overhead medians are 7.236 and 7.290 µs;
all rungs pass the 50% overhead-share eligibility threshold. The adjusted
ratio is `(PARI median − overhead median) / Hex median`, with construction
and serialization still charged to PARI. Values below are ranges across the
two accepted pairs; ratios retain the PARI/Hex convention above.

| n | Hex median ms | PARI median µs | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---:|
| 2 | 0.955–0.966 | 28.924–29.080 | 0.02994–0.03046 | 0.02245–0.02282 |
| 3 | 1.271–1.275 | 34.069–34.375 | 0.02672–0.02704 | 0.02105–0.02131 |
| 4 | 1.761–1.765 | 39.551–39.616 | 0.02241–0.02250 | 0.01831–0.01836 |
| 6 | 2.849–2.857 | 119.987–121.588 | 0.04212–0.04256 | 0.03958–0.04001 |
| 8 | 4.285–4.297 | 47.611–48.016 | 0.01111–0.01118 | 0.00942–0.00948 |
| 12 | 8.695–8.767 | 74.756–75.037 | 0.00856–0.00860 | 0.00773–0.00777 |

The additional already-monic normalization variant (`9c6234e8e`) is **not
retained**. Both accepted pairs improve factorization (1.012–1.013× at degree
24 and 1.131–1.159× at degree 2), but replay is inconsistent: 16.271 to
16.367 ms in one pair (0.6% slower), and 16.283 to 16.074 ms in the other.
The registered rule requires improvement in both canonical replay medians.
The complete negative retention decision and all rejected attempts remain in
the manifest. This is an inconclusive replay effect, not evidence of a
repeat-range-disjoint regression, and the criterion was not relaxed afterward.

The original baseline commit is an ancestor of the retained GitHub PR ref
`refs/pull/10077/head`. Unrelated graph-isomorphism changes between source
checkpoints are outside the tower benchmark's computational imports. Saved
binary hashes identify the executables; harness checkout metadata is not used
as a substitute for their source provenance.
The tag `bench/issue-10074-measured` preserves the measured source history
across the integration rebase onto the upstream `natDegree` API rewrite.

The archived runners identify the code that collected each series. The final
validator separately rechecks all 28 accepted exports after collection and
records seven `*-validated-decision.json` artifacts, including raw min/median/max
values, source/binary consistency, accepted host status, and opposite arm
orders. The six comparisons of retained implementations qualify;
the additional normalization comparison does not.

### Integrated executable

The integrated implementation at `2ae8157bc` includes the upstream
`natDegree` API rewrite. The accessor is an inline abbreviation of the old
expression, but generated code and the executable hash differ. A separate
preregistered comparison measures this actual integrated binary against the
original executable. Attempts 4 and 6 pass on CPU 27/sibling 75 and CPU
32/sibling 80, respectively, with opposite arm orders. All four earlier
attempts are rejected on host telemetry and remain archived. Every Hex and
fresh PARI hash matches; the complete series satisfies the retention rule.

| operation | original median ms | integrated median ms | paired speedup |
|---|---:|---:|---:|
| factor, degree 2 | 1.068–1.071 | 0.956–0.959 | 1.116–1.117× |
| factor, degree 3 | 1.462–1.465 | 1.2747–1.2754 | 1.146–1.149× |
| factor, degree 4 | 2.065–2.077 | 1.760–1.771 | 1.173× |
| factor, degree 6 | 3.571–3.594 | 2.856–2.864 | 1.251–1.255× |
| factor, degree 8 | 6.157–6.169 | 4.305–4.318 | 1.429–1.430× |
| factor, degree 12 | 16.314–16.376 | 8.746–8.837 | 1.853–1.865× |
| factor, degree 24 | 250.261–250.559 | 33.540–33.691 | 7.43–7.47× |
| check, degree 24 | 124.749–124.879 | 16.302–16.414 | 7.60–7.66× |

The paired PARI 2.17.3/cypari2 2.2.4 control has protocol-overhead medians
7.209 and 7.252 µs. All six rungs remain below the 50% overhead-share ceiling.
These ratios use the same PARI/Hex convention and overhead subtraction as
above; they describe the integrated binary, not an extrapolation from the
earlier comparison.

| n | Hex median ms | PARI median µs | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---:|
| 2 | 0.956–0.959 | 28.950–29.073 | 0.03028–0.03030 | 0.02274 |
| 3 | 1.2747–1.2754 | 34.057–34.242 | 0.02672–0.02685 | 0.02103–0.02120 |
| 4 | 1.760–1.771 | 39.172–39.293 | 0.02212–0.02233 | 0.01803–0.01823 |
| 6 | 2.856–2.864 | 120.981–123.319 | 0.04237–0.04306 | 0.03983–0.04054 |
| 8 | 4.305–4.318 | 47.705–47.719 | 0.01105–0.01108 | 0.00937–0.00941 |
| 12 | 8.746–8.837 | 74.424–74.942 | 0.00848–0.00851 | 0.00766–0.00768 |

## Profile

### Factorization after norm and recovery improvements

The [fresh sampling summary](bench-results/hex-number-field-tower-profile-af7b4d49f.json)
profiles the merged implementation at `af7b4d49f` on the canonical degree-24
Selmer input over `ℚ(√2)`. The binary SHA-256 is
`038b21ce95e7a3c2571d869347206ca3ab4e049633ca700490af9937d7c20b2f`.
Two captures of each public factor/check registration run in the order
factor, check, check, factor. Each uses samply 0.13.1 at 999 Hz and the fixed
child's 5-second batch floor, on a separately selected idle physical core of
`chungus2`. The recorded commands, CPU/sibling samples, child hashes, raw
profile/symbol hashes, and exact capture/analysis scripts are in the summary.
Raw profiles and a copy of the executable remain under
`/tmp/tower-factor-profile-af7b4d49f*`.

These are whole-main-thread shape diagnostics, including warmup, fixture
preparation, and autotuning. Fixed dispatch does not emit timed-region
sidecars, so calibration residuals and timed-region sensitivity tests are
not available. The 5-second profiling batch is not a change to the registered
2-second benchmark ceiling. Several postflight samples exceed 5% utilization;
these captures supply no before/after timing verdict. All four expected result
hashes match. The captures contain 16,646–17,614 sampled stacks, classify
99.78–99.82% of leaf samples, and retain the resolved target frame on
99.17–99.76% of stacks. No missing-target samples are renormalized away.

The following are **disjoint phase shares of the whole benchmark thread**,
with ranges across the two captures of each registration. Attribution uses
the recorded call-stack predicates and precedence, rather than summing an
overlapping inclusive ranking.

| phase | factorization | standalone replay |
|---|---:|---:|
| resultant computation | 31.95–32.32% | 32.78–32.82% |
| recovery, including shifts and gcd | 26.09–26.18% | 26.74–26.78% |
| shifted bivariate norm construction | 19.36–19.66% | 19.82–20.00% |
| recursive rational factorization | 10.80–10.93% | 11.30–11.38% |
| squarefreeness outside the preceding phases | 3.98–4.01% | 5.35–5.42% |
| Yun production and checking | 3.36–3.48% | 0% |
| other target work | 3.29–3.52% | 3.38–3.47% |
| target frame absent | 0.24–0.83% | 0.37–0.40% |

The four largest phase shares differ by at most 0.37 percentage points
between repeated captures of the same operation. Recovery itself splits
into shifts (16.02–16.16% of the factorization thread), gcd (9.30–9.41%),
normalization (0.62–0.70%), and other recovery work (0.01–0.04%). Thus the
first-remainder optimization leaves substantial work in both shifts and gcd.

The independent inclusive ranking puts `DensePoly.mulImpl` at
roughly two thirds of the factorization thread, `Arithmetic.mulCoords` at
50.16–50.30%, and `Arithmetic.addCoords` at 23.32–23.44%. These arithmetic
costs occur inside several phases and must not be added to the table.
`Factor.check` accounts for 48.41–48.80% of the factorization capture;
the separately profiled checker has almost the same phase distribution.
Replay therefore repeats the dominant norm and recovery work. Its share is
an overlapping context measurement, not another phase to add to the total.

Leaf categories across the four complete captures are allocation/free
41.59–42.84%, Lean runtime/standard-library operations 28.90–29.48%, GMP
22.30–23.51%, repository code 5.51–5.78%, and unclassified 0.18–0.22%.
Within factorization, allocation leaves under norm construction and resultant
work account for 23.09–23.24% of all samples; recovery contributes another
11.24–11.26%. This points to reducing intermediate arithmetic and storage in
those phases, rather than treating allocator cost as an unrelated phase.
The separately retained initial captures corroborate the phase ordering but
show more variation between allocation and runtime leaf categories; the
initial sequence stopped at a hash-format comparison in postprocessing, not
a failed benchmark result. The complete replication compares hashes numerically.

### Profile-guided factorization changes

1. **Singleton-norm recovery.** When the recursively factored accepted norm
   has one certified irreducible factor, return the canonical monic component
   directly. The recovery product proves exact agreement with the original
   gcd result and transfers its irreducibility theorem to the component. This
   removes the entire recovery phase for singleton norms, including shifting. The [independent untimed PARI check](bench-results/hex-number-field-tower-profile-af7b4d49f-norm-check.json)
   finds one irreducible norm factor at every registered Selmer rung
   `2, 3, 4, 6, 8, 12, 24`, so the condition applies to this family.
   Multiple-factor norms retain ordinary recovery.
2. **Bounded-degree norm construction.** Keep the generator degree below the
   defining degree during Horner evaluation. For the quadratic fixture this
   means computing `A(X) + Y B(X)` modulo `Y² - 2`, then using
   `A² - 2B²` for the norm. The target is the combined 51.31–51.98% norm
   construction/resultant phase. Exact norm equivalence is proved for every
   quadratic relation `Y² + bY + a` over a validated lower tower; other degrees
   retain the general resultant. A guard for a provably repeated shift-zero norm is
   another possible local experiment, but these profiles do not isolate its
   cost, so no saving is attributed to it.
3. **Explicit irreducibility evidence.** If replay remains expensive after
   the first two changes, retain the successful shift and recursively
   checkable norm evidence so the checker need not repeat factorization
   search. This requires a new certificate design, while retaining checked
   reconstruction, multiplicities, and irreducibility.

Scalar inversion and monic normalization are lower priorities on this input:
their inclusive factorization shares are 2.77–2.94% and 1.74–1.78%, respectively.
The previously tested already-monic shortcut remains excluded by its timing
decision. Direct modular number-field factorization is a larger algorithmic
project; absolute-presentation caching needs deeper-tower fixtures.

The phase shares identify work to attack, not attainable speedups. The first
two changes are implemented and measured below; explicit irreducibility evidence
remains a possible follow-up. Independent, combined, and marginal comparisons
cover public factorization and replay, with reducible and recursive-tower
correctness cases and every timing attempt retained.
The [experiment protocol](hex-number-field-tower-factor-protocol.md#singleton-recovery-and-quadratic-norm-experiments)
requires differential correctness checks and a performance decision before
developing correspondence proofs; only proved and verified candidates may
merge. No new exponent or wall-time model follows from this profile.

### Singleton recovery and quadratic norm comparisons

The [preregistered protocol](hex-number-field-tower-factor-protocol.md#singleton-recovery-and-quadratic-norm-experiments)
compares both prototypes independently with computational baseline
`af7b4d49f661a23debf82960bfff3c78435ff135`. These are local, shared-host,
fixed-input constant comparisons; they make no new complexity claim.

| Isolated candidate | Source | Accepted attempts | Degree-24 factor speedup | Degree-24 replay speedup |
|---|---|---|---|---|
| Singleton recovery | `3ba418905` | 1, 9 | 1.347–1.348× | 1.357× |
| Quadratic norm | `af91cca87` | 2, 10 | 1.841–1.867× | 1.889–1.894× |

Both candidates pass the stronger gate: both canonical medians improve in
both accepted, opposite-order pairs; each canonical repeat range is separated
from its baseline in at least one pair; hashes match; and no smaller rung has
a repeat-range-disjoint regression. The
[singleton decision](bench-results/tower-singleton-quadratic/issue-10074-singleton-af7-decision.json)
and [quadratic decision](bench-results/tower-singleton-quadratic/issue-10074-quadratic-af7-decision.json)
retain all sixteen per-case comparisons. Every attempted export and host
record is retained alongside those decisions, including rejected pairs and
arms rejected before their paired run could start. Timing values never select
which pairs are admitted.

The singleton candidate returns the monic input only after the accepted norm
has been recursively factored into one factor. The quadratic candidate keeps
two lower-field polynomial accumulators modulo `Y² + bY + a` during the shift
and computes `A² - bAB + aB²`; other top degrees retain the resultant path.
Neither candidate removes public certificate replay.

The combination at `4209945bc` also passes the stronger gate against the common
baseline, including fresh PARI and overhead measurements. Its
[decision](bench-results/tower-singleton-quadratic/issue-10074-combined-af7-decision.json)
admits opposite-order attempts 1 and 9. Canonical factorization medians fall
from 33.15–33.18 ms to 9.116–9.131 ms (3.634–3.637×); replay medians fall from
16.14–16.40 ms to 4.171–4.199 ms (3.845–3.932×). These are directly measured
combined gains, not products of the isolated speedups.

Both marginal effects also pass the stronger gate. Adding the quadratic norm
to singleton recovery gives a further 2.691–2.709× factorization and
2.840–2.864× replay speedup
([accepted attempts 5 and 6](bench-results/tower-singleton-quadratic/issue-10074-combined-singleton-decision.json)).
Adding singleton recovery to the quadratic norm gives a further 2.006–2.051×
factorization and 2.119–2.154× replay speedup
([accepted attempts 4 and 6](bench-results/tower-singleton-quadratic/issue-10074-combined-quadratic-quiet-decision.json)).
The latter uses the preregistered sustained-quiet replication after the
[original series](bench-results/tower-singleton-quadratic/issue-10074-combined-quadratic-decision.json)
exhausted twelve attempts with only one admitted pair and no verdict. The
replication tightens preflight to thirty consecutive quiet seconds; it keeps
the binaries, cases, performance gate, and all other admission rules fixed.

The [validation record](bench-results/tower-singleton-quadratic/validation.json)
records saved executable hashes and correctness checks. Each isolated variant
and their combination matches the frozen reference on 31 complete canonical
factorizations and checker results, rejects corrupted multiplicities, and
matches 750 full norm arrays. The grid includes nonzero linear terms in the
quadratic relation, rational denominators, signed shifts, a lower quadratic
field, and cubic fallback. All 49 benchmark checks, byte-identical fixtures,
and the nine PARI oracle cases pass. These checks establish experimental
correctness coverage. The companion additionally proves the quadratic Horner
invariant and exact equality with the reference resultant, including arbitrary
quadratic linear terms and recursive lower fields. The singleton recovery
product identifies the returned canonical factor exactly. The existing public
factorization soundness, completeness, monicity, and replay theorems build with
both branches. Before rebasing, the proof-complete build at `4d6608de3` had the identical
SHA-256 hash (`f6feab89…`) to the measured combined prototype. The integrated
executable has hash `9c51c94c…` and its separate comparison follows below.

### Integrated singleton and quadratic implementation

The proof-complete implementation is rebased onto main `064902321` and
compared with a newly built baseline from that main revision, using the
[preregistered integrated comparison](hex-number-field-tower-factor-protocol.md#integrated-implementation-comparison).
The [decision](bench-results/tower-singleton-quadratic/issue-10074-integrated-main-decision.json)
admits opposite-order attempts 2 and 4 and passes the stronger gate. Attempts
1 and 3 remain excluded by host telemetry and are retained in full. All eight
Hex cases improve with disjoint repeat ranges in both admitted pairs, all
hashes match, and all fifteen Hex/PARI/control registrations complete.

Degree-24 factorization medians fall from 34.108–34.120 ms to 9.041–9.096 ms
(**3.750–3.774×**). Replay falls from 16.628–16.678 ms to 4.166–4.167 ms
(**3.991–4.002×**). These are direct comparisons of the final integrated
executables, not products of earlier gains. Both binaries pass all 49
benchmark checks. The restored candidate has exactly the saved measured
binary hash; the full companion and conformance build, differential checks,
fixture comparison, and nine PARI oracle cases pass.

Fresh PARI comparisons from those same candidate runs follow. Ranges enclose
the two admitted medians or paired ratios; they are not confidence intervals.
The protocol-control medians are 7.251–7.262 µs, subtracted only from PARI in
the adjusted ratio. The comparator remains informational; these local
shared-host fixed-input results make no complexity claim.

| n | Hex median (ms) | PARI median (µs) | PARI/Hex raw ratio | Overhead-adjusted ratio |
|---:|---:|---:|---:|---:|
| 2 | 0.635–0.638 | 28.985–29.060 | 0.0455–0.0457 | 0.0342–0.0342 |
| 3 | 0.757–0.761 | 34.372–34.662 | 0.0452–0.0458 | 0.0356–0.0362 |
| 4 | 0.991–1.008 | 39.130–39.485 | 0.0388–0.0398 | 0.0316–0.0325 |
| 6 | 1.391–1.396 | 121.578–121.776 | 0.0872–0.0874 | 0.0820–0.0822 |
| 8 | 1.856–1.860 | 47.747–48.012 | 0.0257–0.0259 | 0.0218–0.0220 |
| 12 | 3.421–3.425 | 75.060–75.139 | 0.0219–0.0220 | 0.0198–0.0198 |

The subsequent merge of rational-function work at main `5ca950a2b` updates
lean-bench to `8a37daf1…`. Both rebuilt tower binaries pass correctness checks,
but their hashes differ, so the comparison above is not a verdict for that
harness revision. The [first harness integration series](bench-results/tower-singleton-quadratic/issue-10074-integrated-harness-decision.json)
ends at twelve attempts with only pair 4 admitted and **no performance
verdict**. All attempted runs and their rejecting host telemetry are retained.
A separately preregistered replication adds a whole-host preflight ceiling
and two quiet minutes. Its [initial collection](bench-results/tower-singleton-quadratic/issue-10074-integrated-harness-quiet-decision.json)
reaches the preflight deadline before any timed arm and has no verdict. Its
[unchanged retry](bench-results/tower-singleton-quadratic/issue-10074-integrated-harness-quiet-retry-decision.json)
admits one pair before the reverse-order preflight times out, so it also has no
verdict. Graph-only integration at main `9fdda65ba` leaves that saved candidate
hash unchanged, as checked by a full tower rebuild.

Main `ac24c7832` subsequently adds shared `HexBasic` code, changing the tower
executable. The final comparison therefore rebuilds both sides from this exact
base. The baseline SHA-256 is `5700c6bd…`; the candidate built from `dbdb01ead`
is `e01da6b4…`. The first collection rejects an arm at postflight and then
times out in preflight, so it remains an incomplete record. The separately
preregistered [final retry](bench-results/tower-singleton-quadratic/issue-10074-integrated-final-main-retry-decision.json)
admits its first two attempts in opposite order and **passes** the stronger
gate. All hashes match, every Hex median improves in both pairs, no smaller rung
has a repeat-range-disjoint regression, and both canonical candidate ranges
are separated below their baseline ranges.

| operation | main median ms | candidate median ms | paired speedup |
|---|---:|---:|---:|
| factor, degree 2 | 0.975–0.976 | 0.640–0.642 | 1.519–1.523× |
| factor, degree 3 | 1.284–1.287 | 0.763–0.765 | 1.679–1.687× |
| factor, degree 4 | 1.785–1.789 | 0.991–0.998 | 1.792–1.801× |
| factor, degree 6 | 2.880–2.884 | 1.399–1.405 | 2.052–2.059× |
| factor, degree 8 | 4.287–4.335 | 1.874–1.877 | 2.288–2.310× |
| factor, degree 12 | 8.802–8.805 | 3.448–3.465 | 2.540–2.554× |
| factor, degree 24 | 33.324–33.633 | 9.129–9.212 | **3.650–3.651×** |
| check, degree 24 | 16.259–16.390 | 4.186–4.199 | **3.872–3.915×** |

Fresh PARI controls from those admitted candidate arms use PARI 2.17.3 and
cypari2 2.2.4. Protocol-overhead medians are 7.250–7.271 µs. The comparator
remains informational and the ratios retain the PARI/Hex convention.

| n | Hex median ms | PARI median µs | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---:|
| 2 | 0.640–0.642 | 29.069–29.334 | 0.0453–0.0458 | 0.0340–0.0345 |
| 3 | 0.763–0.765 | 34.464–34.474 | 0.0451–0.0452 | 0.0356–0.0357 |
| 4 | 0.991–0.998 | 39.026–39.157 | 0.0391–0.0395 | 0.0318–0.0322 |
| 6 | 1.399–1.405 | 121.994–122.490 | 0.0872–0.0872 | 0.0820–0.0820 |
| 8 | 1.874–1.877 | 47.711–48.059 | 0.0254–0.0256 | 0.0216–0.0218 |
| 12 | 3.448–3.465 | 75.171–75.202 | 0.0217–0.0218 | 0.0196–0.0197 |

After this collection, rebasing onto main `71d7d06bf` integrates the Conway
table work. Rebuilding both sides preserves their executable hashes exactly
(`5700c6bd…` and `e01da6b4…`), so the comparison above applies unchanged to
the final integrated code.

### Rational squarefreeness

The [sampling summaries](bench-results/hex-number-field-tower-factor-profiles-b4a02beaf.json)
are unfiltered fixed-benchmark-thread shape diagnostics, including autotuning,
and make no timing claim. GMP accounts for 79.98% of baseline leaf samples
and 23.86% of candidate leaf samples. Missing GMP ancestors leave only 46.60%
of baseline samples in the resolved `factor?` frame, versus 99.33% for the
candidate, so these are not renormalized into comparable within-target shares.
In the candidate capture, recovery occupies 26.61%, shifted norm construction
20.54%, integer factorization 10.00%, and the modular rational squarefreeness
predicate 2.05% of the whole thread. Checked replay is still 48.56% inclusive;
its work overlaps those phases. These shares motivate the isolated recovery and norm-construction
comparisons above without attributing the original loss to certificate
checking alone.

The captured helper is named `Norm.ratSquarefreeFast` at source `b4a02beaf`;
the same implementation is now `ZPoly.ratSquarefreeFast` in the shared
Berlekamp–Zassenhaus library. The source and binary provenance remains attached
to the captures.

### Phase-4 profile coverage

samply 0.13.1 sampled at 999 Hz on the same `chungus2` hardware (Linux
x86-64 6.12.100, AMD EPYC 9455 48-Core Processor, 96 logical CPUs), Lean
4.34.0-rc2, and LeanBench 0.1.0. Every fixture is deterministic and no runtime
oracle participates in any profiled route. Multiplication retains its earlier
timed-region-filtered capture from binary `d9fc6d73f`; its algorithm code is
unchanged. Recursive inversion was refreshed from clean commit `fda376fa0` on
the normalized monic chain. Dense `toPrimitive` was refreshed
from clean pre-rebase commit `6a4911dbb` (now `1c7dc9c1a`) after its quadratic
model failed. Negation was captured from clean pre-rebase binary `86d54d9fa`.
Its negation registration and executable negation path match rebased commit
`7db1a55be`; the benchmark file's unrelated dense-`toPrimitive` registration
changed in an upstream commit during the rebase.
at dimension 448 after exact-width construction removed the normalization
copy. The factorization family was refreshed from the
pre-rebase binary `5d4cb88ad` (bench source byte-identical to `7ad34c201`) at
its canonical mode-3 degree-24 input. The commands were:

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerMulLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerInvLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerNegLadder    448 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runToPrimitiveLadder  9 5000000000   # the dense diagnostic ladder, since replaced by runToPrimitiveDense
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
| `tower-coordinate-arithmetic` | `runTowerInvLadder` n=12 | 3,585 / 67 | 0.888 ms | GMP 40.25%, allocation 38.08%, Lean runtime 19.89%, own code 1.65% | 99.86% |
| `tower-coordinate-arithmetic` | `runTowerNegLadder` D=448 | 3,661 / 120,654 | 0.746 ms | Lean runtime 56.76%, own code 25.62%, allocation 17.54%, other 0.08% | 99.92% |
| `split-flatten` | `runToPrimitiveLadder` n=9 | 3,651 / 124,055 | 0.870 ms | GMP 44.67%, allocation 38.84%, Lean runtime 15.09%, own code 0.60% | 99.21% |
| `trager-factorization` | `runTowerFactorLadder` degree 24 (raw fixed capture) | 16,325 / n.a. | n.a. | GMP 74.54%, Lean runtime 15.34%, allocation 9.21%, own code 0.78% | 99.87% |
| `adjoin-extend` | `runAdjoin` (raw fixed capture) | 13,786 / n.a. | n.a. | allocation 46.44%, GMP 27.26%, Lean runtime 24.05%, own code 2.01% | 99.75% |
| `split-flatten` | `runSplit` (raw fixed capture) | 9,985 / n.a. | n.a. | Lean runtime 40.01%, allocation 37.91%, GMP 13.52%, own code 7.83% | 99.27% |
| `split-flatten` | `runFlatten` (raw fixed capture) | 18,762 / n.a. | n.a. | allocation 37.74%, Lean runtime 37.06%, GMP 20.47%, own code 4.47% | 99.74% |

The four retained filtered captures pass calibration (residuals 0.51 to 0.87 ms
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
defining polynomial. Recursive inversion at dimension 24: 97.82% in
`Hex.NumberTower.inv`/`Arithmetic.invCoords`, dominated by the monic extended
gcd `Hex.DensePoly.xgcdLeftMonicAux` (94.34%) whose inner work is lower-field
multiplication (`Arithmetic.mulCoords` 86.42%, splitting into `convolve`
54.84% and `reduce` 21.62%, with `addCoords` at 29.18%) and polynomial
division (`DensePoly.divMod` 24.41%). The capture verifies that the normalized
chain spends its time in the constant number of lower-field products and
inversions the untimed replay counts, and that polynomial division, which
carried 63.61% of the unnormalized chain, is no longer the dominant phase.
Both phases named by the SPEC's arithmetic section are the measured cost;
nothing is unattributed.

Negation at dimension 448 retains 98.93% of samples in the registered public
target. Overlapping inclusive shares are 59.14% in the exact generated helper
`_private.Init.Data.Array.Basic.0_Array.ofFn.go`, 28.38% in
`Arithmetic.negCoords`, 22.97% in `Rat.neg`, and 13.22% in the structural
coordinate checksum. Allocation accounts for 17.54% of leaf samples. The
former `normalizeCoeffs` reconstruction copy is absent, confirming that the
timed path now consists of the source-derived coordinate traversal,
exact-width wrapper, and full result hash.

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
94.92% → the upstream isolation kernel `Hex.ZPoly.isolateComplexRoots?`/`isolateLoop` 95.15%,
with `Hex.taylor` 69.37% and dyadic Gauss arithmetic (`GaussDyadic.mul`
46.63%) as the leaf work; `Internal.extend?` (level validation) is 31.88%
and factor selection `selectFactor?` 63.62%. The factorization step itself
is not visible at this input because the quartic factors immediately; the
cost is the SPEC's embedding invariant being enforced (`adjoin?` "selects
the unique irreducible factor that vanishes at the requested AlgebraicRoot
under the current embedding"). The isolation kernel that dominates is the
same `Hex.ZPoly.isolateComplexRoots?` measured by HexNumberField's and HexRoots' registered
isolation ladders; its asymptotic evidence lives in those upstream reports,
and the tower-level boundary is measured end to end by the registered
`runAdjoin`/`runAdjoinIdentity` cases.

### `split-flatten`: isolation again, through both entry points

`runSplit`: 99.90% inside `Hex.NumberTower.splitAux`; root retention and
adjoining dominate through the same disambiguation path
(`RawEvaluation.vanishesAt?` 66.97%, `Hex.ZPoly.isolateComplexRoots?` 64.55%), with the
remainder in the tower factorization it repeats after each extension.
`runFlatten`: 97.93% inside the target, 97.36% in
`Hex.NumberTower.flatten?`, dominated by the primitive-element candidate
search `Flatten.searchRecoveredAux` 90.20% whose cost is
`Flatten.candidateAt?` → `Hex.AlgebraicPoly.Common.shift?` 83.22% (the
integer eliminant of `θ + cα`) and the canonical exactification
`Hex.AlgebraicRoot.exact?` 61.83%, both running the upstream `Hex.ZPoly.isolateComplexRoots?`
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
| [merged factor/replay profiles](bench-results/hex-number-field-tower-profile-af7b4d49f.json) | clean `af7b4d49f`; repeated degree-24 factorization/replay shapes and untimed singleton-norm check | per-capture core/sibling telemetry; whole-thread shape only | `f22f3eef9401d2956bb84d3935ee1c1ddf6fb25704d03e640409011085308d5c` |
| [factor follow-up manifest](bench-results/hex-number-field-tower-followup-manifest.json) | original `b8602c76a`, modular `8dd0f8e15`, isolated and combined variants; all accepted/rejected exports, exact runners, and validated decisions | paired core/sibling telemetry; local comparison evidence | `0603c1f6b46b63b64ec78725c9c02ec532473fc556c1425b21f4d6a8b9a6bc09` |
| [original mode-1 export](bench-results/hex-number-field-tower-phase4-final-mode1-ce03eb89-chungus2-cpu19.json) | clean pre-rebase `ce03eb89b` (same patch now `9a9fe1e26`); passing unaffected models | [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | `65275d1f2dfb6fd41e1a962d44d27bc843ab75ed8a2d5a305df2d2aed7c4bfbb` |
| [superseded fixed calibration](bench-results/hex-number-field-tower-phase4-final-mode3-ce03eb89-chungus2-cpu19.json) | clean pre-rebase `ce03eb89b` (same patch now `9a9fe1e26`); retained measurements, but the negation/division/forward-map rows are not admissible mode-3 evidence | [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | `391d48365634eb9cc3b02eb8801920e13034bc537777d6ebc6d5f2834769426e` |
| [superseded seven-case mode-3 export](bench-results/hex-number-field-tower-phase4-final-mode3-d277c583-chungus2-cpu19.json) | clean pre-rebase `d277c583` (same patch now `c720b4aca`); earlier canonical-case calibration retained for provenance | [matching postflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | `dcae0daaac0470764794b793606a005a83c845dd9af44a80f61ddad97e593f06` |
| [constructor-only rerun](bench-results/hex-number-field-tower-phase4-final-ofq-e63e3a589-chungus2-cpu19.json) | clean pre-rebase `e63e3a589` (same patch now `77513c3b6`); passing constructor model | [matching postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | `f703055985a9b4f25b69bd954d7072f08b505896cc1625ad7ec98e102f55f65b` |
| [extended ordered-mode diagnostic](bench-results/hex-number-field-tower-phase4-mode1-nine-and-constructor-diagnostic-d277c583-chungus2-cpu19.json) | clean pre-rebase `d277c583` (same patch now `c720b4aca`); superseded nine-case/constructor diagnostic | CPU 19 | `9bea0ee7378b3cf8b71bccb200cdf09e92085b8806ef4d19bab704c25e92b793` |
| [d277 postflight](bench-results/hex-number-field-tower-phase4-host-state-d277c583-chungus2-cpu19.json) | host state paired with the d277 exports | sampled CPU and SMT sibling | `cbb9ae6f454ed300d51e10dfb01f7454b568bde45b74e6a7b033b2b55b22c8d8` |
| [e63 postflight](bench-results/hex-number-field-tower-phase4-host-state-e63e3a589-chungus2-cpu19.json) | host state paired with the constructor rerun | sampled CPU and SMT sibling | `79d70f64f57983dfed82d96732510106b5ae54aabe304c309d3e90c80f366738` |
| [repaired forward-map export](bench-results/hex-number-field-tower-phase4-to-primitive-db22ebe6-chungus2-cpu19.json) | clean pre-rebase `db22ebe6c` (now `8c5e38f39`); original cubic model after the executable zero-coordinate fix | CPU 19 | `1b835e4c87b65aa7e0c520178991ea8b6a0975a911d4c5a7b5bcc1d63c42661a` |
| [repaired forward-map profile](bench-results/hex-number-field-tower-to-primitive-profile-08c17a18-chungus2.json) | clean pre-rebase `08c17a18c` (now `bcab4e402`); timed-region-filtered dimension-18 full-basis map | CPU 19 | `56739b12f292aad4085814d206730d0c67f4337949d8603b7faf5df810ff9f18` |
| [dense forward-map export](bench-results/hex-number-field-tower-dense-to-primitive-85f9c303-chungus2-cpu16.json) | clean pre-rebase `85f9c303f` (now `27033e761`); five trials at every `n = 2, 3, 4, 5, 6, 9` rung | CPU 16, selected idle with sibling 64 | `b54946d132c1ff1d29895cbe77661b4d244dc5792716152b2c9cb664517f120b` |
| [corroborating dense export](bench-results/hex-number-field-tower-dense-to-primitive-5f4bab2f-chungus2-cpu1.json) | clean pre-rebase preregistration commit `5f4bab2fc` (now `7d0624a33`); same inconclusive verdict and β = +1.023 | CPU 1; no paired idle-core sample | `4e6bdf834eb2e98ead56ac84f46da08eacd78c51ecd60ecf947af67b66df36f0` |
| [dense forward-map profile](bench-results/hex-number-field-tower-dense-to-primitive-profile-6a4911db-chungus2.json) | clean pre-rebase `6a4911dbb` (now `1c7dc9c1a`); timed-region-filtered dimension-18 dense public map | unpinned shape capture | `5dadec1dfefc811addb7e7ae242f88d81ab3880f91a19570356e4e92402cd7f9` |
| [recursive arithmetic diagnostics](bench-results/hex-number-field-tower-phase4-recursive-arithmetic-8af75849-chungus2-cpu19.json) | clean pre-rebase `8af758494` (now `a965ee906`); checked reordered height-two family on the unnormalized chain; pre-repair diagnostic | CPU 19 | `90a52359c542a1708acb68d845daf9be5bea1ca7ce7dfaf9b467309b94024efd` |
| [negation and recursive-factor diagnostics](bench-results/hex-number-field-tower-phase4-final-mode-diagnostics-959489aa-chungus2-cpu19.json) | clean pre-rebase `959489aa2` (same patch now `eeb360ef8`); final ordered-mode attempts | CPU 19 | `1bdfb6b3f0f65808c8a1e6f2cf5698420ebb54931cdfcb1b449afc13e56dcf03` |
| [division and forward-map diagnostics](bench-results/hex-number-field-tower-phase4-final-div-map-diagnostics-dd5ef519-chungus2-cpu19.json) | clean pre-rebase `dd5ef5197` (same patch now `cb6583d3a`); final ordered-mode attempts, with its sparse `runToPrimitiveLadder` block superseded by the dense export | CPU 19 | `d965dfde3919c9eaab2f15d505b4cca43b8d0d38b95e1130db5d93901590f52a` |
| [negation calibration](bench-results/hex-number-field-tower-opus-calibration-605abcb5-chungus2-cpu19.json) | clean pre-rebase `605abcb5` (same branch state now `2ed1aba5d`); registered linear diagnostic, β = −0.162 | CPU 19 | `360bcf931e5171183ae25ddba16d6ff3edbb820bab5d40fd4c0de1908919f5a8` |
| [preregistered 100 ms negation failure](bench-results/hex-number-field-tower-negation-preregistered-100ms-9e17fb58-chungus2-cpu19.json) | clean `9e17fb582`; the seven-rung schedule before exact-width reconstruction, β = +0.414 | CPU 19 | `1be091b9afc75190418d939f4476b2aed6b17846996474407d4f1df1a3f47354` |
| [ordered-mode diagnostics](bench-results/hex-number-field-tower-phase4-mode3-diagnostics-b2ebf281-chungus2-cpu1.json) | clean pre-rebase `b2ebf281b` (same patch now `eaa691fc9`); temporary executable diagnostics | CPU 1 | `6f3182498feec6f8b4d7fb121f5cd67fb5b1ba011117b1e72e3431217981270d` |
| [CPU-19 postflight](bench-results/hex-number-field-tower-phase4-host-state-ce03eb89-chungus2-cpu19.json) | final measurement protocol | sampled CPU and SMT sibling | `f8a9d1d8294f59cf1bce18e02a2baae57728c87db24f5e96cc1c5c0e884a5a76` |
| [canonical factor profile](bench-results/hex-number-field-tower-phase4-final-factor-profile-5d4cb88a-chungus2.json) | pre-rebase binary `5d4cb88ad` (same patch now `842043ebf`); algorithm source unchanged | unpinned shape capture | `f34c803bc741a92b9ac5b6040b107aa80c206f9a8b1d6515635ca6af5d3c9cf2` |
| [factor degree diagnostic](bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json) | clean `7d6c0c50a`; rejects the former envelope | CPU 13 | `c0ae3da96fe41f36a87ed6665bf98cd1b2d4c9c209b541a7a0516cbdb28f9d30` |
| [component anchors](bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json) | clean `3f23d6425`; hash/attribution only | CPU 13 | `1927e8268c5ac22a1df0e987db5dff878e7ccdcc448252d21b6ee6240689f156` |
| [PARI pairs](bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json) | clean `322f53b15`; identical comparator sources | CPU 13 | `5c60e35f20265683fff0eb01f397e3355957fcd0737f0ca21e7781a0b30f0a3f` |
| [coordinate profile summaries](bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json) | archived clean `d9fc6d73f` multiplication binary; captured multiplication source matches current `8ea8d6819` | unpinned shape capture | `31767bff125621d07391e151bc613a3a1c8ee7b74300a81fd7029af2198b505c` |
| [pre-repair recursive-inversion profile](bench-results/hex-number-field-tower-recursive-inversion-profile-8ea8d681-chungus2.json) | clean `8ea8d6819`; timed-region-filtered reordered family at dimension 24 | CPU 19 | `91e67ce7b3764578fec8d2bcf7011f1ec489399871937c04442e3a4e222bbe43` |
| [repaired inversion export](bench-results/hex-number-field-tower-recursive-arithmetic-800bd23da-chungus2-cpu16.json) | clean `800bd23da`; five trials of the inversion ladder on the monic chain (β = −0.010) and the division ladder diagnostic (β = +0.191) | CPU 16; three-second `/proc/stat` postflight 0.33% busy | `7996b6f0f4e69336a0ea21d1e0e5c949defb51dd53b03f80546a06f306f75a9f` |
| [normalized-chain inversion profile](bench-results/hex-number-field-tower-recursive-inversion-profile-fda376fa0-chungus2.json) | clean `fda376fa0`; timed-region-filtered monic chain at dimension 24, 3,585 retained samples | unpinned shape capture | `39b2fbf8c4143f307056d0d7a1db0f68f972cddf21f5d314fabf270ae5c36165` |
| [mode-3 division and dense-map export](bench-results/hex-number-field-tower-mode3-division-dense-map-900e3aad8-chungus2-cpu3.json) | clean `900e3aad8`; three repeats of each canonical case under its ceiling | CPU 3, selected idle; three-second preflight 2.33% and postflight 1.33% busy | `ccc168aa1b8f71d810199550a4e03ea7e64e4f9be8a9c5760830a728ed1fb152` |
| [inversion chain replay](bench-results/hex-number-field-tower-inv-chain.csv) | clean `800bd23da`; untimed per-step counts and heights of the monic top-level chain on every rung | not a timing | `2bac8d4fb4f1ca041607637355b5970d6c26922dcf0f404d8116b26d31d71951` |
| [division chain replay](bench-results/hex-number-field-tower-div-chain.csv) | clean `fda376fa0`; untimed divisor-inversion and product-by-inverse limb work per rung | not a timing | `20c7c01a2d6cbc86fca01f42c3c038411c324adec5d4055385e8c00ee036b45f` |
| [dense map image replay](bench-results/hex-number-field-tower-to-primitive-images.csv) | clean `2850b5321`; untimed primitive-image heights and fixture cost per rung of the dense schedule | not a timing | `d9074d9964c51eab8424477eadcf6e771fe6903a146abdb8476d24e4a0d09311` |
| [negation mode-1 export](bench-results/hex-number-field-tower-negation-linear-86d54d9fa-chungus2-cpu3.json) | clean pre-rebase `86d54d9fa`; its negation registration and executable path match rebased `7db1a55be`, while the unrelated dense-`toPrimitive` registration differs; five trial-major repeats | CPU 3 | `c9c71a5cb9a54b82c4a9b88cf2ccc03f6f0f304639afb05085899aa256552edc` |
| [negation core telemetry](bench-results/hex-number-field-tower-negation-telemetry-86d54d9fa-chungus2-cpu3.json) | continuous core/sibling trace filtered to 481 timed regions; ratio 0.001888 | CPU 3 and SMT sibling 51 | `6e8a3b36ce08a77f73cb5eb0fab18614c48ab7608270808b6a1a7c28c3e9eb45` |
| [rejected negation export](bench-results/hex-number-field-tower-negation-linear-rejected-86d54d9fa-chungus2-cpu3.json) | first of at most two unchanged attempts; timing verdict passed but interference grade rejected the run | CPU 3 | `b1d8a568aec107fa57359d07610229bbcc1e38c22a76b147aa2ab4be8f0c324a` |
| [rejected negation telemetry](bench-results/hex-number-field-tower-negation-telemetry-rejected-86d54d9fa-chungus2-cpu3.json) | 481 timed regions; interference ratio 0.003274 exceeded the 0.002 ceiling | CPU 3 and SMT sibling 51 | `0564f704333a9527e3bfd605326cd6d6d3104053b6b5aaa610790c88ef958357` |
| [negation allocation counts](bench-results/hex-number-field-tower-negation-allocation-counts-86d54d9fa.json) | five repeated small-allocation counts at dimensions 128 and 256 plus an empty-body control | unpinned count diagnostic | `2c3c386e854dddf50ef021ce53cb908985400595f7c51ebae936ebbff38b0f85` |
| [negation inclusive profile](bench-results/hex-number-field-tower-negation-profile-86d54d9fa-chungus2.json) | clean pre-rebase `86d54d9fa`; negation sources match rebased `7db1a55be`; timed-region-filtered dimension-448 public negation and hash | unpinned shape capture | `b69714a5a9e9dce3562ba0137c73e3e8ef30a7718c4caf595ff33bffc17493e0` |
| [factor baseline](bench-results/hex-number-field-tower-factor-baseline-b8602c76a.json) | `b8602c76a`; saved baseline binary; unimported draft makes harness git-dirty | local diagnostic | `c18855d828c15207f3603a5f40858cb2305b607a9b5ee40d6796582ffb6124f4` |
| [contaminated factor candidate](bench-results/hex-number-field-tower-factor-contaminated-b4a02beaf.json) | clean `b4a02beaf`; first candidate and fresh PARI pairs | local diagnostic | `b8e10d2bf4d7e8a0c7bddef83976bd9bedb9e531a31c877759265f872d31e29e` |
| [first comparison host metadata](bench-results/hex-number-field-tower-factor-contaminated-host-b4a02beaf.json) | CPU 13/sibling 61; failed postflight | local diagnostic | `35437ab094a2c39e19964964cbb09b7e82dcd8513184034e570e1b84f06a06eb` |
| [second factor baseline](bench-results/hex-number-field-tower-factor-contaminated-baseline2-b8602c76a.json) | clean `b8602c76a` detached checkout; saved baseline binary | local diagnostic | `f273467b752f5f70486866a868c4926ea6dac29479fc9fdbc2b678d8380711eb` |
| [second comparison host metadata](bench-results/hex-number-field-tower-factor-contaminated-host2-20ff1f2f9.json) | CPU 13/sibling 61; failed baseline postflight, candidate skipped | local diagnostic | `e25432e5962f8db66cd962a82f825fbf9c75e2e459dd44a9df3a0971fee5c5d1` |
| [third factor baseline](bench-results/hex-number-field-tower-factor-contaminated-baseline3-b8602c76a.json) | clean `b8602c76a` detached checkout; saved baseline binary | local diagnostic | `479546a46c90bee2a89257c2571777d845006c5122bad6627a348a4c5a327683` |
| [third comparison host metadata](bench-results/hex-number-field-tower-factor-contaminated-host3-0faa834dc.json) | CPU 1/sibling 49; failed baseline postflight, candidate skipped | local diagnostic | `4c982ad715541892a9440957972ae22bc22b682171237f16e6393d068eba1d17` |
| [factor coefficient heights](bench-results/hex-number-field-tower-factor-heights-b4a02beaf.csv) | clean `b4a02beaf`; untimed exact remainder replay | local diagnostic | `028f998f4e7eba2ab9807215357e247e6e0ebb62d7b25bb29289eefd8cdb57bc` |
| [factor comparison profiles](bench-results/hex-number-field-tower-factor-profiles-b4a02beaf.json) | baseline binary from `b8602c76a`, candidate from `b4a02beaf`; raw hashes embedded | local diagnostic | `5a0ff9630bd3e1db8e5b7ee64dde6fde990f85570a1cc08bf13737d63c3e8ef7` |

The evidence comprises the single-root bounded-height fixtures, eight passing
mode-1 surfaces, nine independently budgeted mode-3 surfaces, the untimed
chain and image replays that attribute the repaired inversion and the two
mode-3 arithmetic surfaces, explicit retry and recursive-relative branch
exercise, and an inclusive canonical factor profile. The component, protocol,
hash, and comparator exports retain only their stated roles. No advertised
surface lacks an admissible mode.

Toolchain: Lean 4.34.0-rc2, LeanBench 0.1.0, samply 0.13.1, PARI 2.17.2,
and cypari2 2.2.4. Reference host: `chungus2`, Linux x86-64, AMD EPYC 9455
48-Core Processor, 96 logical CPUs.

## Verification

The computational and Mathlib tower libraries build, all 49 bench checks pass,
and emitted fixtures remain byte-for-byte identical. The PARI oracle checks
nine cases with no failures. Added regressions cover both bad-prime branches,
rational denominators, repeated polynomials, zero/constants, and rejection of
corrupted public factorization scalars and multiplicities. Recovery guards
cover exact and nonzero first remainders and each fallback condition over
rationals and towers of heights one and two; the Mathlib proof establishes
equality with the reference gcd, including its remaining fuel.

The final selected implementation passes
`lake build HexNumberFieldTowerMathlib HexNumberFieldTower.Conformance
hexnumberfieldtower_emit_fixtures hexnumberfieldtower_bench` (9,698 jobs).
The selected pre-rebase benchmark executable is byte-identical to the verified
and measured combined executable from `8d54c7158`, SHA-256
`d78f6616e823004c807ebcbd343656629e43857e8a3286827cf0293a8c905034`.
The integrated build also passes all 9,698 jobs, all 49 benchmark checks,
byte-identical fixtures, and nine PARI oracle cases. Its measured executable
has SHA-256
`c3e2de0cb83c2ab3e7fb68997c06778ed8a2369f63c4f21878ec88d7ce3c10a6`.
All 49 checks include the six PARI comparators using the registered provider.
The export validator's 19 unit tests pass and run in the existing CI job.

### Reference verification

- `lake build HexNumberFieldTower HexNumberFieldTower.Conformance
  hexnumberfieldtower_emit_fixtures`: pass.
- `lake exe hexnumberfieldtower_bench list`: 8 parametric plus 41 fixed
  registrations.
- `lake exe hexnumberfieldtower_bench verify`: the 43 Lean registrations
  pass on the reference checkout; the six `runPariNfFactor*` comparator
  registrations need cypari2, which that checkout does not have, and their
  sources are unchanged.
- Emitted Tower fixtures match the committed JSONL byte for byte; the PARI
  oracle checks 9 cases with 0 failures.
- `python3 scripts/check_phase4.py`: pass.
- `python3 scripts/check_dag.py`: pass.

## Concerns

None.
