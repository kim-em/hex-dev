# HexNumberField Performance Report

`HexNumberField` is a compiled-track library: every operation it advertises is
Mathlib-free executable computation, so all of its Phase-4 evidence is ordinary
LeanBench evidence and none of it is fresh-module proof evidence
(`PLAN/Phase4.md` §Evidence tracks).

This snapshot records the state of that evidence as measured; it is **not** a
Phase-4 completion claim. `libraries.yml` keeps `HexNumberField` at
`done_through: 3`. §Concerns says why.

## Bench targets

The compiled Mathlib-free driver is `bench/HexNumberField/Bench.lean`. It
registers 9 controlled parametric targets and 34 fixed targets (43 total).
The adjacent comments in the driver derive each model from the work performed
inside the timed function; the models below are copied from the registration
sites.

| target | operation and controlled input | declared model |
|---|---|---|
| `runQAdjoinAddLadder` | `QAdjoin` addition in `ℚ(2^(1/n))`, both operands dense and all-nonzero | `n` |
| `runQAdjoinMulLadder` | `QAdjoin` multiplication, then reduction modulo `X^n - 2` | `n * n` |
| `runQAdjoinInvLadder` | `QAdjoin` inversion by rational extended gcd against `X^n - 2` | `n * n * (Nat.log2 (n + 2) + 1)` |
| `runAddEliminantLadder` | `ZPoly.addEliminant (X^n - 2) (X^2 - 3)`, the Brown sum-eliminant resultant | `n * n * (Nat.log2 (n + 2) + 1)` |
| `runLazyAddLadder` | end-to-end `AlgebraicRoot.add?` pairing the first root of `X^n - 2` with `√3` | `n ^ 5 * (Nat.log2 (n + 2)) ^ 2` |
| `runExactLadder` | `AlgebraicRoot.exact?` on a root of `(X^n - 2)(X + 3)` | `n ^ 9 + n ^ 7 * (Nat.log2 (n + 2)) ^ 2` |
| `runCommonPresentationLadder` | `AlgebraicPoly.Common.presentation?` over `n + 1` canonical coefficients | `n` |
| `runQAdjoinRootsLadder` | `QAdjoin.roots?` on `g^2 * (X - 1)` over `ℚ(√2)` with `g` dense of degree `n` | `n ^ 5 * (Nat.log2 (n + 2)) ^ 2` |
| `runAlgebraicRootsLadder` | `AlgebraicPoly.roots?` on a dense degree-`n` polynomial with one `√2` coefficient | `n ^ 5 * (Nat.log2 (n + 2)) ^ 2` |

The 34 fixed registrations are nine canonical API cases (`runFixedMul`,
`runFixedInv`, `runFixedMinpoly`, `runAddEliminant`, `runIsolateAdd`,
`runSelectAdd`, `runLazyAdd`, `runExact`, `runRoots`), twenty-four Lean/PARI
comparator rungs (`runQAdjoinMulPair` / `runPariPolmodMul` at
`n = 4, 6, 8, 12, 16, 20` and `runQAdjoinInvPair` / `runPariPolmodInv` at
`n = 4, 6, 8, 10, 12, 16`), and one external-driver overhead probe
(`runPariPolmodOverhead`).

### Fixture control

Every parametric fixture here — the arithmetic operands, and the
`AlgebraicPoly` coefficients behind the common-field and algebraic-root
ladders — builds coefficient `i` from one helper, `denseRatCoeff`, whose
numerator cycles modulo 11 and denominator modulo 6. Every denominator is in
`1 .. 6`, so the reduced common denominator divides
`lcm(1, ..., 6) = 60` and stays under six bits at every degree measured. The
coefficient pattern has period 66, so it repeats in the
degree-128 arithmetic rungs and the 128-coefficient `AlgebraicPoly` rungs;
repetition does not change any coefficient's height, which is what these
controlled one-parameter models depend on.

Holding height fixed is what makes these one-parameter ladders. An earlier
form built coefficient `i` as `±(i + salt + 1) / (i + 2)`. Because
`gcd (i + salt + 1) (i + 2) = gcd (salt - 1) (i + 2)`, that reduces to
denominator `(i + 2) / gcd (i + 2) (salt - 1)`, whose lcm over the vector
still has `Θ(n)` bit length — it differs from `lcm (2, …, n + 1)` only by
divisors of the constant `salt - 1`. So those ladders varied coefficient
height together with degree and could not test any fixed-height cost model.

One caveat on the multiplication model: bounded input coefficients do not make
every rational operation single-limb, since the convolution accumulators grow
by `O(log n)` bits. The declared `n^2` is a coefficient-operation count over
the measured domain, where those accumulators stay within a machine word.

### Scientific arithmetic ranges

The arithmetic fixtures now certify only the selected positive real root of
`X^n - 2`. Integer Newton iteration supplies an untrusted Mahler-precision
dyadic approximation, and HexRoots' local `isolateOne?` entry point checks the
single atom directly. The certificate still says that its region contains
exactly one simple root; it no longer constructs and pairwise-separates the
other `n - 1` roots.

The addition and multiplication ladders consequently cover six doublings,
`n = 4, 8, 16, 32, 64, 128`. Degree 128 is a common controlled domain whose
timed multiplication remains in the millisecond regime. The inversion ladder
covers `n = 4, 8, 16, 32, 48, 64, 96`; its ceiling is set by the timed extended
gcd, which takes about 3.25 s there: a useful upper asymptotic rung that
remains practical to sample. These are scientific operation ranges, not
fixture-wallclock caps.

### Track assignment re-audit

`HexNumberField` advertises no elaboration, tactic, emitted-proof or
kernel-checking surface, so every advertised operation belongs to the
Mathlib-free compiled row of `PLAN/Phase4.md` §Evidence tracks and none of
them is eligible for the fresh-module proof row.

Re-auditing the SPEC's API-surface code blocks against the registrations
above, the following advertised compiled operations have no registration:
`QAdjoin.approx`; `QAdjoin` subtraction, negation, `Div` and the rational
scalar actions; `QAdjoin.toAlgebraicNumber?` / `toAlgebraicNumber`;
`AlgebraicNumber.canonicalRep?` and `zeroRep`; `AlgebraicRoot.sub?`, `mul?`,
`div?`, `inv?` and `neg`; the whole of `AlgebraicNumber` arithmetic (`add`,
`sub`, `mul`, `neg`, `inv`, `div`, `ofRat`, `Pow Nat`, `Pow Int`, the `SMul`
actions and the numeric casts); `AlgebraicRoot.isZero`,
`AlgebraicNumber.isZero` and `RefinedIsolation.containsZero`;
`AlgebraicPoly.ofArray`, `coeff`, `size`, `degree?`, `isZero` and `beq`;
`Disambiguation.evalMajorant`; and every member of the
`Hex.AlgebraicPoly.Common` namespace below `presentation?` (`signedShift`,
`rational?`, `add?`, `mul?`, `scale?`, `shift?`, `degree`, `extendShiftStep`,
`extendShift?`, `extend?`, `primitive?`, `powers?`, `trace?`,
`coordinates?`).

The Attribution rule adds three more, and these were found by profiling
rather than by reading the SPEC — §Profile has the evidence. `QAdjoin.roots?`
spends 83.04% of a call in `Roots.mergeRootList` → `mergeRoot` → `sameValue?`,
`AlgebraicRoot.exact?` spends 95.58% in `exactFactor?`'s candidate
re-isolation and 47.39% in `AlgebraicNumber.canonicalRep?`, and
`QAdjoin.Roots.componentRoots?` is 91.45% of `AlgebraicPoly.roots?`. None of
those phases has a registration of its own. The two phases the
`runQAdjoinRootsLadder` derivation singles out — `Roots.normEliminant` and
`Roots.evalEliminant` — turn out not to be dominant on any profiled family,
but they are separable and asymptotically significant, so they are owed
registrations too.

These gaps are recorded in §Concerns. They do not affect any measurement
below; they bound what the measurements are entitled to conclude about the
library as a whole.

## Verdicts

Authoritative verdict per ladder, and which committed run it comes from. The
runs below give the measurements; this table says which one counts.

| target | verdict | slope | from |
|---|---|---:|---|
| `runQAdjoinAddLadder` | **consistent** | -0.067 | single-root |
| `runQAdjoinMulLadder` | **consistent** | -0.005 | single-root |
| `runQAdjoinInvLadder` | inconclusive, slower | **+1.790** | single-root |
| `runAddEliminantLadder` | **consistent** | +0.115 | fixture-corrected |
| `runLazyAddLadder` | **consistent** | -0.123 | quiet-heavy |
| `runExactLadder` | inconclusive, faster | — | quiet |
| `runCommonPresentationLadder` | **consistent** | -0.245 | fixture-corrected |
| `runQAdjoinRootsLadder` | inconclusive, slower | — | quiet-heavy |
| `runAlgebraicRootsLadder` | inconclusive, faster | — | fixture-corrected |

Five fit their declared models. The four that do not are §Concerns entries,
each with a filed issue; none of them is a measurement artefact, and §Profile
shows that three are cases where the declared model names a phase that is not
where the time goes.

Five parametric runs are committed: one full-suite pass, two idle-host
re-measurements that between them cover all nine ladders, and a
fixture-corrected run plus the single-root run that supersede six of those.
§Artefact traceability
records the source commit and SHA-256 of each, and says which supersedes
which.

The **full-suite run** covers all nine ladders at three outer trials per rung:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runLazyAddLadder \
  Hex.NumberFieldBench.runExactLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific.json
```

`chungus2` is shared, and other work on it drove the one-minute load average
from 105 to above 150 during that run. The bench child held a full core
throughout, and a uniform slowdown cancels in a log-log slope fit, but
transient spikes do not: `runQAdjoinMulLadder` recorded a 48% three-trial
spread at its top rung and `runAddEliminantLadder` 65% at `n = 128`.

The **quiet run** therefore re-measures the ladders that fit inside a short
window, at five outer trials, with the host idle (load average 1.5). Two of
its six entries — `runAddEliminantLadder` and `runCommonPresentationLadder` —
were later superseded by the fixture-corrected run below and are omitted from
the table:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runExactLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-quiet.json
```

Quiet run, worst per-rung spread now at or below 5.5%:

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runQAdjoinAddLadder` | 4, 6, 8, 12, 16, 24 | **consistent** | -0.054 | 109.4..120.6 | 4.96% |
| `runQAdjoinMulLadder` | 4, 6, 8, 12, 16, 24 | **consistent** | -0.009 | 467.5..473.6 | 3.51% |
| `runQAdjoinInvLadder` | 4, 6, 8, 12, 16, 20 | inconclusive | **+1.038** | 473.4..1624.1 | 1.84% |
| `runExactLadder` | 2, 3, 4, 6, 8 | inconclusive | — | 2.014..174.6 | 5.49% |

`runQAdjoinMulLadder`'s full-suite verdict was `inconclusive` at `+0.222`
solely because of the load spike at `n = 24`; on the idle host its `C` is flat
to 1.3% across all six rungs.

The **single-root run** refreshes all three fixed-field arithmetic ladders
after their fixture and scientific domains changed:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runQAdjoinAddLadder \
  Hex.NumberFieldBench.runQAdjoinMulLadder \
  Hex.NumberFieldBench.runQAdjoinInvLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-single-root.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runQAdjoinAddLadder` | 4, 8, 16, 32, 64, 128 | **consistent** | -0.067 | 95.97..113.61 | 2.38% |
| `runQAdjoinMulLadder` | 4, 8, 16, 32, 64, 128 | **consistent** | -0.005 | 459.92..471.40 | 22.55% |
| `runQAdjoinInvLadder` | 4, 8, 16, 32, 48, 64, 96 | inconclusive | **+1.790** | 597.2..50344.2 | 16.02% |

Addition remains linear through 128 and multiplication remains quadratic
through 128. Inversion's monotone normalized cost grows even more clearly over
the repaired range: the extended ladder strengthens the existing #9721
finding rather than attributing the former ceiling to its fixture.

A second quiet run covers the three ladders too expensive to fit in the same
window, at three outer trials, on the idle host:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runLazyAddLadder \
  Hex.NumberFieldBench.runQAdjoinRootsLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-quiet-heavy.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runLazyAddLadder` | 2, 3, 4, 6, 8, 10 | **consistent** | -0.123 | 64088..107864 | 0.92% |
| `runQAdjoinRootsLadder` | 2, 3, 4, 6, 8 | inconclusive | — | 1.134e6..2.016e6 | 3.57% |
| `runAlgebraicRootsLadder` | 3, 4, 5, 6, 8 | inconclusive | — | 80829..184738 | 1.48% |

The two root ladders reproduce the full-suite run almost exactly
(`runQAdjoinRootsLadder` 1.134e6..2.016e6 against 1.176e6..2.013e6;
`runAlgebraicRootsLadder` 80829..184738 against 80419..185225), so their
verdicts do not depend on host conditions. `runLazyAddLadder` improves from
`-0.300` to `-0.123` once the load-induced spike at its 113 s top rung is
gone, so its consistent verdict is no longer marginal against its declared
0.35 tolerance.

Between the two quiet runs, every one of the nine ladders has an idle-host
measurement, and the full-suite export is retained as the first pass.

A **fixture-corrected run** closes out the three ladders whose inputs or
schedules changed in review. `prepAlgPolyInput` still built coefficient `i` as
`(i + 1) / (i + 2)` after `denseRatCoeff` was fixed, so the two ladders it
feeds were still varying coefficient height with degree; it now shares the
bounded-height helper. `runAddEliminantLadder` and
`runCommonPresentationLadder` also had their low rungs restored, so each
covers the range its downstream caller actually uses rather than starting
above the start-up-dominated regime:

```sh
.lake/build/bin/hexnumberfield_bench run \
  Hex.NumberFieldBench.runAddEliminantLadder \
  Hex.NumberFieldBench.runCommonPresentationLadder \
  Hex.NumberFieldBench.runAlgebraicRootsLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-phase4-scientific-fixture-corrected.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runAddEliminantLadder` | 4, 8, 16, 32, 64, 128, 256 | **consistent** | +0.115 | 91.8..168.1 | 1.46% |
| `runCommonPresentationLadder` | 2, 4, 8, 16, 32, 64, 128 | **consistent** | -0.245 | 7.771e6..1.823e7 | 5.18% |
| `runAlgebraicRootsLadder` | 3, 4, 5, 6, 8 | inconclusive | — | 64309..234783 | 3.11% |

Restoring the low rungs costs margin and buys coverage, which is the right
trade: `runAddEliminantLadder` moves from `+0.015` over `16 .. 256` to
`+0.115` over `8 .. 256` against a 0.15 tolerance, and
`runCommonPresentationLadder` from `+0.027` over `16 .. 128` to `-0.245` over
`4 .. 128` against its declared 0.35 tolerance. Both still fit their unchanged
declared models, now over ranges that include the degrees their callers use.

`runAlgebraicRootsLadder` moves the other way. On the uncontrolled fixture its
continuous-proxy slope was `-0.490`; with bounded coefficient height it is
`-1.406`, because the old fixture's growing coefficients were inflating the
large-`n` end. That is recorded as a finding, not as a pass —
https://github.com/kim-em/hex-dev/issues/9728.

### Reading the three ladders with no fitted slope

`fitSlope` rejects a log-log fit whose x-range is too narrow, and these three
ladders span under two octaves because their top rungs already cost 0.3 s,
594 s and 25 s per call. The harness then falls back to a multiplicative
range check, `cMax / cMin ≤ exp(slopeTolerance · xRange)`. That check is
sensitive to a discontinuity anywhere in the ladder, and
`(Nat.log2 (n + 2)) ^ 2` supplies one: it is an integer step function, so the
declared model jumps by 2.25x in a single rung — between `n = 5` and `n = 6`
for `runAlgebraicRootsLadder`.

Recomputing `C` against a continuous asymptotic proxy — the same expression
with real `log₂` in place of `Nat.log2` — separates that artefact from the
residual. `Nat.log2` and real `log₂` are different functions at these rungs,
so this is a sensitivity check and not a restatement of the declared model:
the registrations are unchanged, and every official verdict quoted in this
report is the harness's, computed against the registered integer model. The
harness bound is reproduced in the table only to show the scale of the
artefact, not as a verdict on the proxy.

| target | integer-log cMax/cMin | smooth-log cMax/cMin | bound | smooth-log slope |
|---|---:|---:|---:|---:|
| `runLazyAddLadder` | 1.683 | 1.199 | 1.524 | -0.028 |
| `runExactLadder` | 86.697 | 80.498 | 1.410 | **-4.145** |
| `runQAdjoinRootsLadder` | 1.777 | 1.953 | 1.410 | **+0.675** |
| `runAlgebraicRootsLadder` | 2.680 | 2.680 | 1.275 | **-1.406** |

(Quiet-run figures, except `runAlgebraicRootsLadder`, which is the
fixture-corrected run. The full-suite run gives -0.205, -4.143 and +0.641 for
the first three, so none of those readings depends on host conditions.)

Read as a sensitivity check. On the uncontrolled fixture most of
`runAlgebraicRootsLadder`'s spread was the step; with bounded coefficient
height the residual is large under either evaluation and the step no longer
explains it. `runQAdjoinRootsLadder`'s does not shrink — its `C` is monotone under either
evaluation, with spreads at or below 3.6%, and it deviates in the
slower-than-declared direction. `runExactLadder`'s declared envelope
over-predicts by roughly four powers of `n` under either evaluation. Both
remain `inconclusive` on the harness's own verdict; nothing here reclassifies
them.

### Fixed registrations

All 30 fixed registrations in the committed comparator export agree across
repeats, and all ten with a declared `expectedHash` match it. Medians from the
committed
[comparator export](bench-results/hex-number-field-phase4-comparators.json):

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runFixedMul` | 39.844 us | `0xc319ee2337214e59` | match |
| `runFixedInv` | 137.423 us | `0x1525969728101d06` | match |
| `runFixedMinpoly` | 4.039 ms | `0xb1ed00ebc8d039e9` | match |
| `runAddEliminant` | 5.754 us | `0xeb2eecad44116a79` | match |
| `runIsolateAdd` | 9.649 ms | `0x4367ab34a73ea4ed` | match |
| `runSelectAdd` | 11.193 ms | `0xb2956b93cac0235f` | match |
| `runLazyAdd` | 9.899 ms | `0xb2956b93cac0235f` | match |
| `runExact` | 1.421 ms | `0xafd3fbfd3a66fc82` | match |
| `runRoots` | 1.069 ms | `0x927e3f02f6eee94` | match |
| `runPariPolmodOverhead` | 7.126 us | `0x0` | match |

The SPEC's §Complexity and Phase 4 budgets caps a compiled degree-10 field
operation at 100 ms on the reference host. `runFixedMul` is 39.844 us and
`runFixedInv` is 137.423 us, both about three orders inside that budget.

`runSelectAdd` and `runLazyAdd` produce the same hash and the same median to
within 0.1%, which is the intended reading: the SPEC asks Phase 4 to separate
eliminant construction, isolation and disambiguation, and the trio
`runAddEliminant` (5.754 us), `runIsolateAdd` (9.649 ms) and `runSelectAdd`
(11.193 ms) does that. Construction is three orders below isolation, and
operation-ball disambiguation adds 1.5 ms on top of isolation — about 16%.
Isolation dominates the lazy-addition cost.

## Comparator ratios

The library SPEC declares one external comparator, **PARI/GP via cypari2**,
class `informational`, scoped to the fixed-field arithmetic bench targets.
PARI's `t_POLMOD` arithmetic (`Mod(a, m) * Mod(b, m)` and `Mod(a, m)^(-1)`) is
the callable PARI surface computing exactly `QAdjoin` multiplication and
extended-gcd inversion in `ℚ[x]/(m)`. It is wired as a persistent-subprocess
process call through `scripts/oracle/pari_bench_driver.py` and
`Hex/BenchOracle/Pari.lean`, with per-rung fixed Lean/PARI registration pairs
on identical deterministic inputs.

`libraries.yml` declares no second comparator, so
`SPEC/benchmarking.md` §Headline reports requires no comparator-runtime plot.

**Differential correctness.** Both sides hash the identical reduced rational
coefficient vector, so `compare` joins them on result hashes. Every shared
rung agrees, which makes this comparator a cross-implementation conformance
check as well as a timing one.

**Per-call overhead.** `runPariPolmodOverhead` issues one `polmod`-family
request whose PARI-side work is a constant `0`, so it measures the JSON
request/reply round trip alone. Its median is **7.126 us** (min 6.750 us,
max 7.164 us across five repeats). Overhead is at most 22% of the PARI wall
time on the smallest rung of either family and under 4% on the largest, so
every rung clears the 50% floor `SPEC/benchmarking.md` sets for the eligible
range, and every rung is far inside the 10 s hard ceiling and the 1 s soft
target. Both raw and overhead-adjusted ratios are recorded below; the adjusted
figure subtracts only that request/reply floor, leaving serialization and
PARI-side polynomial construction charged to PARI.

**Eligible range and rung density.** `SPEC/benchmarking.md` warns that a
doubling-only schedule usually does not give enough eligible rungs to read a
trend, and both families here cross the ratio 1 inside the measured range —
a claim three points cannot support. The registered schedules are therefore
densified with in-fill rungs: multiplication at `n = 4, 6, 8, 12, 16, 20`
and inversion at `n = 4, 6, 8, 10, 12, 16`, each bracketing its crossover.

The local single-root fixture removes the former smoke-cost constraint. The
registered comparison domains now restore multiplication at `n = 20` and
inversion at `n = 16`, giving six rungs in each family. The committed table
below records the earlier five-rung comparator run; the added endpoints retain
the same paired inputs and result-hash agreement checks.

Ratios are quoted as PARI wall time divided by Hex wall time, so a value above
1 means Hex is faster.

### QAdjoin multiplication against PARI `Mod(a, m) * Mod(b, m)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 7.399 us | 39.058 us | 18.2% | `0xdbf17509eb46ddc0` | 5.279x | 4.316x |
| 6 | 17.332 us | 40.824 us | 17.5% | `0x2cf024c7e6988530` | 2.355x | 1.944x |
| 8 | 30.356 us | 57.391 us | 12.4% | `0x195da6835711d63` | 1.891x | 1.656x |
| 12 | 67.972 us | 70.731 us | 10.1% | `0xffbc782c4aba338b` | 1.041x | 0.936x |
| 16 | 120.729 us | 89.841 us | 7.9% | `0x5e40c901cf3a60b9` | 0.744x | 0.685x |

### QAdjoin inversion against PARI `Mod(a, m)^(-1)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 19.951 us | 33.460 us | 21.3% | `0xb8302e29a4df3f41` | 1.677x | 1.320x |
| 6 | 69.026 us | 54.823 us | 13.0% | `0xc80c3d019e0b9e4c` | 0.794x | 0.691x |
| 8 | 141.853 us | 218.302 us | 3.3% | `0xd16df20a45d683c7` | 1.539x | 1.489x |
| 10 | 251.376 us | 215.512 us | 3.3% | `0x7d0941f1c8c5f9e8` | 0.857x | 0.829x |
| 12 | 505.466 us | 253.295 us | 2.8% | `0x7776688d262fc467` | 0.501x | 0.487x |

### Trend

Both ratios decline monotonically in the large: multiplication from 5.279x at
`n = 4` to 0.744x at `n = 16`, crossing 1 just past `n = 12`
(1.041x raw, 0.936x adjusted); inversion from 1.677x at `n = 4` to 0.501x at
`n = 12`. The two declines have different causes, and only one of them is a
statement about arithmetic.

For **multiplication** the decline is PARI's fixed per-call marshalling being
amortised, not an algorithmic-class difference. Fitting each side's growth
across the six rungs, with the 7.126 us driver floor subtracted from PARI:

- Hex grows as `n^2.01` — its declared `n^2` model, measured on the same
  inputs as the ladder.
- PARI's net cost grows as `n^0.72`, and its net times are 31.9, 33.7, 50.3,
  63.6 and 82.7 us.

A sub-linear exponent means PARI's `t_POLMOD` multiplication is not what is
being timed: at these degrees the cost is building and reading back the
`O(n)`-coefficient objects, which cypari2 charges per coefficient. The
comparison does not yet reach degrees where PARI's arithmetic dominates its
own marshalling, so the multiplication ratio is orientation only. That is
consistent with the SPEC's declared expectation for this comparator — "the
constant-factor gap is structural rather than algorithmic" — and it is why
this comparator is `informational` rather than `gating`.

For **inversion** the decline is real. Both sides do substantial work at
every rung, and their exponents differ by a full power of `n`:

- Hex grows as `n^2.86`.
- PARI's net cost grows as `n^2.24`, with net times 26.3, 47.7, 211.2, 208.4
  and 246.2 us.

This is a diverging trend rather than a constant-factor gap, so it sits
against the comparator's declared expectation, and it points the same way as
the internal ladder: `QAdjoin.inv` grows faster than its declared model, and
it also grows faster than PARI's implementation of the same operation on the
same inputs. The exponent difference should be read as indicative rather than
precise — PARI's net cost jumps discontinuously between `n = 6` and `n = 8`,
so a six-point fit through it is not a clean measurement of PARI's asymptotics.
What survives that caveat is the direction and the fact that the ratio falls
by more than a factor of three across the ladder, which is what coefficient
swell in the unnormalised rational extended gcd predicts. Recorded against
https://github.com/kim-em/hex-dev/issues/9721 rather than as a separate
Concern.

The `n = 6` and `n = 8` inversion rungs are non-monotone (0.756x then 1.525x)
because PARI's own net cost jumps from 45.4 us to 208.4 us between them while
Hex's rises smoothly; that is a PARI-side discontinuity and no claim here
rests on those two points.

### Absence declarations retained

The per-library SPEC declares three surfaces with no comparable PARI unit
surface, all with the reason
`no-comparable-surface-in-named-comparator`, and this report changes none of
them: factorization-lazy and canonical arithmetic (PARI has no certified lazy
algebraic-number type), exactification (PARI exposes rational polynomial
factorization but no unit function certifying the minimal polynomial of a root
given an isolating region), and the root APIs (`nfroots`/`nffactor` return
only roots inside the number field, `polroots` returns uncertified floating
approximations). The measurements above cover exactly the two surfaces PARI
does expose.
## Profile

samply 0.13.1 sampled at 999 Hz on the same `chungus2` hardware (Linux x86-64,
AMD EPYC 9455 48-Core Processor, 96 logical CPUs), Lean 4.34.0-rc2, LeanBench
0.1.0, binary built from source commit `066f6fc29`. Every fixture is
deterministic and no fixture is randomised: the arithmetic operands come from
`denseRatCoeffs` at salts 3 and 7 (and 5 for inversion), and the remaining
families are the fixed polynomials named in the bench source. No runtime
oracle participates in any profiled route.

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinMulLadder     16 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runLazyAddLadder         8 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runExactLadder           8 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runQAdjoinRootsLadder    6 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfield_bench \
  Hex.NumberFieldBench.runAlgebraicRootsLadder  6 5000000000
```

Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexnumberfield_bench`.
Raw filtered `*.json.gz` artefacts stay developer-local under `/tmp` as
`SPEC/profiling.md` requires; their local paths are
`/tmp/hex-profile-<target>-<param>.json.gz`.

One representative case per `phase4.input_families` entry, all five passing
calibration, confidence and the ±5 ms sensitivity check:

| family | case | retained / rejected | calibration residual | leaf cost | classified |
|---|---|---:|---:|---|---:|
| `qadjoin-arithmetic` | `runQAdjoinMulLadder` n=16 | 3,938 / 4,750 | 0.755 ms | allocation 37.79%, GMP 37.51%, Lean runtime 23.72%, own code 0.74% | 99.75% |
| `lazy-arithmetic` | `runLazyAddLadder` n=8 | 25,651 / 153 | 0.293 ms | allocation 50.31%, GMP 32.79%, Lean runtime 13.61%, own code 0.58% | 97.28% |
| `exactification` | `runExactLadder` n=8 | 5,334 / 488 | 0.574 ms | allocation 43.74%, GMP 29.04%, Lean runtime 18.77%, own code 1.78% | 93.33% |
| `fixed-field-roots` | `runQAdjoinRootsLadder` n=6 | 97,109 / 7 | 0.325 ms | allocation 52.60%, GMP 33.21%, Lean runtime 11.54%, own code 0.42% | 97.77% |
| `algebraic-poly-roots` | `runAlgebraicRootsLadder` n=6 | 5,965 / 9 | 0.633 ms | allocation 53.80%, GMP 30.76%, Lean runtime 12.04%, own code 0.54% | 97.14% |

The rejected counts are the untimed fixture preludes, which the filtering
postprocessor excludes by construction. The arithmetic profile predates the
single-root repair, so its rejected samples include the former 4.9 s
all-roots fixture; that prelude is outside the retained timed region.

"Own code" is under 2% everywhere because almost every leaf is a GMP entry
point, a `malloc`/`free`, or a Lean runtime primitive reached from
`Hex.*` frames; the inclusive ranking below is what identifies the hot paths.

### `qadjoin-arithmetic` — attributes cleanly

| share | function |
|---:|---|
| 99.85% | `Hex.QAdjoin.mul` |
| 54.34% | `Hex.DensePoly.mulImpl` |
| 45.35% | `Hex.DensePoly.divMod` → `divModArray` 45.07% → `subtractScaledShiftStep` 42.38% |

This is exactly what the `runQAdjoinMulLadder` derivation describes: dense
schoolbook multiplication of two degree-`(n-1)` operands, then reduction of the
degree-`(2n-2)` product modulo `X^n - 2`. The two phases are 54% and 45% of the
call and both are inside the registered target. Nothing here is unattributed.

### `lazy-arithmetic` — attributes to isolation, as declared

| share | function |
|---:|---|
| 92.11% | `Hex.AlgebraicRoot.ofEliminant?` |
| 92.11% | `Hex.isolate` / `isolateLoop` |
| 86.32% | `Hex.Component.refineAll` / `IsolationLoop.next` |
| 84.83% | `Hex.taylor` |

The `runLazyAddLadder` derivation declares that isolation at separation depth
dominates the eliminant resultant. It does: eliminant construction is the
5.754 us `runAddEliminant` fixed case against a 46 s call, and 92% of the call
is inside `isolate`. This family's registered targets account for its cost.

### `exactification` — the declared phase is not the cost

| share | function |
|---:|---|
| 95.63% | `Hex.AlgebraicRoot.exact?` |
| 95.58% | `Hex.AlgebraicRoot.exactFactor?` |
| 95.28% | `Hex.isolate` / `isolateLoop` |
| 47.39% | `Hex.AlgebraicNumber.canonicalRep?` / `ofNormalized?` |

`runExactLadder` declares the classical BHKS factorization bound
`n^9 + n^7 log^2 n`. The Berlekamp–Zassenhaus factorization does not appear in
the ranking at all. The cost is `exactFactor?`'s re-isolation of the candidate
factors at separation depth plus `canonicalRep?`'s canonical re-isolation —
that is, the certification work `exact?` does *after* factoring. This is why
the declared envelope over-predicts by `n^4.14`, and it is an Attribution-rule
gap: the dominant phase has no registration of its own.

### `fixed-field-roots` — 83% of the call is duplicate removal

| share | function |
|---:|---|
| 90.65% | `Hex.QAdjoin.roots?` |
| 83.04% | `Hex.QAdjoin.Roots.mergeRootList` → `mergeRoot` → `sameValue?` |
| 83.04% | `Hex.AlgebraicRoot.exact?` (reached from `sameValue?`) |
| 41.49% | `Hex.AlgebraicNumber.canonicalRep?` |
| **7.61%** | `Hex.QAdjoin.Roots.componentRoots?` |

The `runQAdjoinRootsLadder` derivation declares that isolation of the
degree-`2n` norm eliminant is the ceiling. That whole phase — norm eliminant,
isolation, disambiguation — lives inside `componentRoots?` and is **7.61%** of
the call. The double resultant `evalEliminant`, which the derivation singles
out as lower order, never enters the ranking (`retainZero?` is 0.67% and
`evalBall?` 0.66%), so that part of the claim holds but is not where the time
went.

The time goes to the final duplicate-removal pass. `mergeRoot` compares
candidates with `sameValue?`, and `AlgebraicRoot` equality takes its slow path
whenever the stored polynomials differ — the SPEC says so in §Equality and
zero: "Otherwise exactify both roots and use canonical `AlgebraicNumber`
equality. The second path can factor twice and is not a fast arithmetic
primitive." The family `g^2 * (X - 1)` produces two Yun components with
different norm eliminants, so every cross-component comparison pays a full
`exact?`. That is both the Attribution-rule violation and the mechanism behind
this ladder's slower-than-declared verdict.

### `algebraic-poly-roots` — the contrast that confirms the mechanism

| share | function |
|---:|---|
| 91.87% | `Hex.isolate` / `isolateLoop` |
| 91.45% | `Hex.QAdjoin.roots?` |
| 91.45% | `Hex.QAdjoin.Roots.componentRoots?` |
| 82.90% | `Hex.taylor` |

The same `QAdjoin.roots?` entry point, profiled on an input with a single
squarefree component, spends 91.45% in `componentRoots?` and never reaches
`mergeRoot`. Isolation really is the cost here, as the shared derivation
claims. The difference between this profile and the previous one is the
cross-component merge, which is what makes the fixed-field family's residual a
finding rather than noise.

## Artefact traceability

| artefact | source commit | host state | SHA-256 |
|---|---|---|---|
| [`bench-results/hex-number-field-phase4-scientific.json`](bench-results/hex-number-field-phase4-scientific.json) | `066f6fc29` | loaded (load average 105 to 150) | `3948bbb7107d96e7af56edcf2497b52e2b2a34f4d89376b93cc477c0f8a6517d` |
| [`bench-results/hex-number-field-phase4-scientific-quiet.json`](bench-results/hex-number-field-phase4-scientific-quiet.json) | `066f6fc29` | idle (load average 1.5) | `186d25381ce87fa6c4f4d0b6d51c03eed8f865a120dd83a5ac278c8d34be6408` |
| [`bench-results/hex-number-field-phase4-scientific-quiet-heavy.json`](bench-results/hex-number-field-phase4-scientific-quiet-heavy.json) | `a2b70b949` | idle | `71b42aaa8b45ce25f450f7b7ad8a0d537c9e2220bdddd8ab79fcb5cc51c477b3` |
| [`bench-results/hex-number-field-phase4-comparators.json`](bench-results/hex-number-field-phase4-comparators.json) | `9ae125c67`, clean tree | idle | `fd42dda533a345815205a0de1737f95cdd9a93e02ae355d78be31cb0bac62041` |
| [`bench-results/hex-number-field-phase4-scientific-fixture-corrected.json`](bench-results/hex-number-field-phase4-scientific-fixture-corrected.json) | the fixture correction (this branch head) | idle | `6a176e351a46436d7c6ae47fff666f62c85b09c549d3d3866697ae3fded4fa6a` |
| [`bench-results/hex-number-field-single-root.json`](bench-results/hex-number-field-single-root.json) | `9cf6087f3`, clean tree | idle | `40fe59b58c62918eec4c0eaa81684a4095f63283bc2a1c2a4fefcd13acd56c92` |

Ladder numbers come from the commits named in the table. Across the first four
the compiled ladder code is identical: `a2b70b949` differs from `066f6fc29`
only in two comments, and `9ae125c67` only changes comparator registrations
and their smoke cost. The
fixture-corrected run is the exception and is the reason it exists — it
supersedes the earlier `runAddEliminantLadder`, `runCommonPresentationLadder`
and `runAlgebraicRootsLadder` numbers, and only those three. The single-root
run supersedes the earlier three fixed-field arithmetic ladders after their
domains expanded. Four of the five
profiles were taken from the `066f6fc29` binary; the `algebraic-poly-roots`
profile was re-taken after the fixture correction. Toolchain throughout:
Lean 4.34.0-rc2, LeanBench 0.1.0, samply 0.13.1, cypari2 driving PARI through
`scripts/oracle/pari_bench_driver.py`. Host throughout: `chungus2`, Linux
x86-64, AMD EPYC 9455 48-Core Processor, 96 logical CPUs.

Every fixture in this library is deterministic; no registration draws from a
random seed, so a rung is identified by its parameter and the salt named in
the bench source rather than by a seed.

## Concerns

`HexNumberField` remains at `done_through: 3`. Phase-4 exit criteria that do
not pass, each tracked:

- **`QAdjoin.inv` grows faster than any declared model absorbs.**
  `runQAdjoinInvLadder` returns the slower-than-declared direction at
  `beta = +1.790` through degree 96 on the idle host with monotone `C`, and
  replaying the shipped `DensePoly.xgcdLeft` recursion shows its
  rational entries reaching about `n^2.1` bits where a monic-normalised chain
  stays near the `n log n` Hadamard bound.
  https://github.com/kim-em/hex-dev/issues/9721 — bench-found: QAdjoin.inv's
  rational extended gcd swells coefficients to Theta(n^2) bits.
- **The advertised API surface is not fully registered.** Roughly thirty
  advertised compiled operations have no `setup_benchmark` or
  `setup_fixed_benchmark`, and `Roots.normEliminant` and `Roots.evalEliminant`
  are separable asymptotically significant phases of `QAdjoin.roots?` that
  nothing measures, so the Attribution rule is not satisfied.
  https://github.com/kim-em/hex-dev/issues/9722 — audit-found: HexNumberField's
  advertised API surface is not fully registered for Phase 4.
- **`QAdjoin.roots?` is slower than its declared isolation ceiling, and the
  declared phase is not the cost.** The ladder's `C` rises monotonically with
  spreads at or below 3.6%, and the profile says why: 83.04% of a call is
  duplicate removal through `mergeRootList` → `sameValue?` →
  `AlgebraicRoot.exact?`, against 7.61% in `componentRoots?`, which is where
  the norm eliminant and its isolation live.
  https://github.com/kim-em/hex-dev/issues/9724 — bench-found: QAdjoin.roots?
  is slower than its declared isolation model by ~n^0.64.
- **`runExactLadder`'s declared envelope names a phase that is not the cost.**
  It runs about `n^4.2` against a BHKS `n^9` envelope, and the profile shows
  the Berlekamp-Zassenhaus factorization the envelope bounds does not appear
  in the ranking at all: 95.58% of the call is `exactFactor?`'s candidate
  re-isolation and 47.39% is `canonicalRep?`.
  https://github.com/kim-em/hex-dev/issues/9725 — audit-found: runExactLadder's
  BHKS envelope names a phase that is not the cost.
- **`AlgebraicPoly.roots?` runs well inside its declared isolation envelope.**
  With a height-controlled fixture the continuous-proxy slope is `-1.406`:
  about `n^4.3` against a predicted `n^5.8`. Unlike the fixed-field ladder,
  the profile confirms the cost is where the derivation says (isolation inside
  `componentRoots?`, 91.45%), so the gap is in the bound rather than the
  phase.
  https://github.com/kim-em/hex-dev/issues/9728 — bench-found:
  AlgebraicPoly.roots? runs about n^4.3 against a declared n^5 log^2 isolation
  envelope.
