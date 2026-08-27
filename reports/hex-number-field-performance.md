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

The parametric arithmetic fixtures build coefficient `i` as a signed rational
whose numerator cycles modulo 11 and whose denominator cycles modulo 6, so the
reduced common denominator of a degree-`n` element stays under six bits at
every degree measured (verified at `n` = 8, 16, 32, 48, 64 for all three salts
in use). Holding height fixed is what makes these one-parameter ladders: an
earlier form built coefficient `i` as `±(i + salt + 1) / (i + 2)`, whose
reduced common denominator is `lcm (2, …, n + 1)` and therefore `Θ(n)` bits, so
that ladder varied coefficient height together with modulus degree and could
not test any fixed-height cost model.

Two ladders are bounded by fixture construction rather than by the operation
they time. `prepFieldInput` and `prepInvInput` build a certified root of
`X^n - 2`, which isolates all `n` complex roots at separation depth: 4.9 s at
`n = 16`, 14.2 s at `n = 20`, 30.8 s at `n = 24`, and over a quarter of an hour
by `n = 32`. Their wallclock caps are sized for that prelude; the timed calls
themselves are microseconds. This is why the QAdjoin arithmetic ladder stops at
`n = 24` and the inversion ladder at `n = 20`.

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
`QAdjoin.Roots.componentRoots?` is 90.32% of `AlgebraicPoly.roots?`. None of
those phases has a registration of its own. The two phases the
`runQAdjoinRootsLadder` derivation singles out — `Roots.normEliminant` and
`Roots.evalEliminant` — turn out not to be dominant on any profiled family,
but they are separable and asymptotically significant, so they are owed
registrations too.

These gaps are recorded in §Concerns. They do not affect any measurement
below; they bound what the measurements are entitled to conclude about the
library as a whole.

## Verdicts

Three parametric runs are committed: one full-suite pass and two idle-host
re-measurements that between them cover all nine ladders. §Artefact
traceability records the source commit and SHA-256 of each; no commit after
`066f6fc29` changes compiled code any ladder number below was measured with.

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

The **quiet run** therefore re-measures the six ladders that fit inside a short
window, at five outer trials, with the host idle (load average 1.5):

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
| `runAddEliminantLadder` | 8, 16, 32, 64, 128, 256 | **consistent** | +0.015 | 139.0..167.0 | 4.11% |
| `runExactLadder` | 2, 3, 4, 6, 8 | inconclusive | — | 2.014..174.6 | 5.49% |
| `runCommonPresentationLadder` | 8, 16, 32, 64, 128 | **consistent** | +0.027 | 7.578e6..8.388e6 | 1.18% |

`runQAdjoinMulLadder`'s full-suite verdict was `inconclusive` at `+0.222`
solely because of the load spike at `n = 24`; on the idle host its `C` is flat
to 1.3% across all six rungs.

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

### Reading the three ladders with no fitted slope

`fitSlope` rejects a log-log fit whose x-range is too narrow, and these three
ladders span under two octaves because their top rungs already cost 0.3 s,
594 s and 25 s per call. The harness then falls back to a multiplicative
range check, `cMax / cMin ≤ exp(slopeTolerance · xRange)`. That check is
sensitive to a discontinuity anywhere in the ladder, and
`(Nat.log2 (n + 2)) ^ 2` supplies one: it is an integer step function, so the
declared model jumps by 2.25x in a single rung — between `n = 5` and `n = 6`
for `runAlgebraicRootsLadder`.

Recomputing `C` against the same declared function evaluated with a real
logarithm separates that artefact from the residual. This is analysis, not a
re-declaration; the registrations are unchanged.

| target | integer-log cMax/cMin | smooth-log cMax/cMin | bound | smooth-log slope |
|---|---:|---:|---:|---:|
| `runLazyAddLadder` | 1.683 | 1.199 | 1.524 | -0.028 |
| `runExactLadder` | 86.697 | 80.498 | 1.410 | **-4.145** |
| `runQAdjoinRootsLadder` | 1.777 | 1.953 | 1.410 | **+0.675** |
| `runAlgebraicRootsLadder` | 2.286 | 1.376 | 1.275 | -0.490 |

(Quiet-run figures. The full-suite run gives -0.205, -4.143, +0.641 and -0.488
for the same four, so none of these readings depends on host conditions.)

So `runAlgebraicRootsLadder`'s apparent failure is mostly the step: its true
residual is a 1.372 range against a 1.275 bound. `runQAdjoinRootsLadder`'s is
not: its `C` is monotone with spreads at or below 2%, and it deviates in the
slower-than-declared direction. `runExactLadder`'s declared envelope
over-predicts by four orders in `n`.

### Fixed registrations

All 34 fixed registrations agree across repeats, and all ten with a declared
`expectedHash` match it. Medians from the committed
[comparator export](bench-results/hex-number-field-phase4-comparators.json):

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runFixedMul` | 40.378 us | `0xc319ee2337214e59` | match |
| `runFixedInv` | 136.756 us | `0x1525969728101d06` | match |
| `runFixedMinpoly` | 4.035 ms | `0xb1ed00ebc8d039e9` | match |
| `runAddEliminant` | 5.802 us | `0xeb2eecad44116a79` | match |
| `runIsolateAdd` | 9.569 ms | `0x4367ab34a73ea4ed` | match |
| `runSelectAdd` | 9.737 ms | `0xb2956b93cac0235f` | match |
| `runLazyAdd` | 9.650 ms | `0xb2956b93cac0235f` | match |
| `runExact` | 1.325 ms | `0xafd3fbfd3a66fc82` | match |
| `runRoots` | 917.475 us | `0x927e3f02f6eee94` | match |
| `runPariPolmodOverhead` | 6.992 us | `0x0` | match |

The SPEC's §Complexity and Phase 4 budgets caps a compiled degree-10 field
operation at 100 ms on the reference host. `runFixedMul` is 40.378 us and
`runFixedInv` is 136.756 us, both about three orders inside that budget.

`runSelectAdd` and `runLazyAdd` produce the same hash and the same median to
within 0.1%, which is the intended reading: the SPEC asks Phase 4 to separate
eliminant construction, isolation and disambiguation, and the trio
`runAddEliminant` (5.802 us), `runIsolateAdd` (9.569 ms) and `runSelectAdd`
(9.737 ms) does that. Construction is three orders below isolation, and
operation-ball disambiguation adds 168 us on top of isolation — under 2%.
Isolation is the whole lazy-addition cost.

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
request/reply round trip alone. Its median is **6.992 us** (min 6.786 us,
max 7.233 us across five repeats). Overhead is at most 22% of the PARI wall
time on the smallest rung of either family and under 4% on the largest, so
every rung clears the 50% floor `SPEC/benchmarking.md` sets for the eligible
range, and every rung is far inside the 10 s hard ceiling and the 1 s soft
target. Both raw and overhead-adjusted ratios are recorded below; the adjusted
figure subtracts only that request/reply floor, leaving serialization and
PARI-side polynomial construction charged to PARI.

**Eligible range and rung density.** `SPEC/benchmarking.md` warns that a
doubling-only schedule usually does not give enough eligible rungs to read a
trend, and both families here cross the ratio 1 inside the measured range —
a claim three points cannot support. The schedules are therefore densified
with in-fill rungs: multiplication at `n = 4, 6, 8, 12, 16, 20` and inversion
at `n = 4, 6, 8, 10, 12, 16`.

Ratios are quoted as PARI wall time divided by Hex wall time, so a value above
1 means Hex is faster.

### QAdjoin multiplication against PARI `Mod(a, m) * Mod(b, m)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 7.381 us | 31.441 us | 22.2% | `0xdbf17509eb46ddc0` | 4.260x | 3.312x |
| 6 | 17.136 us | 40.860 us | 17.1% | `0x2cf024c7e6988530` | 2.384x | 1.976x |
| 8 | 30.558 us | 49.411 us | 14.2% | `0x195da6835711d63` | 1.617x | 1.388x |
| 12 | 67.700 us | 67.715 us | 10.3% | `0xffbc782c4aba338b` | 1.000x | 0.897x |
| 16 | 120.723 us | 86.243 us | 8.1% | `0x5e40c901cf3a60b9` | 0.714x | 0.656x |
| 20 | 189.755 us | 104.261 us | 6.7% | `0xa6b61e5f0a5bbec9` | 0.549x | 0.513x |

### QAdjoin inversion against PARI `Mod(a, m)^(-1)`

| n | Hex | PARI | driver overhead as share of PARI | canonical hash | raw ratio | adjusted ratio |
|---:|---:|---:|---:|---|---:|---:|
| 4 | 20.067 us | 32.819 us | 21.3% | `0xb8302e29a4df3f41` | 1.635x | 1.287x |
| 6 | 69.307 us | 52.366 us | 13.4% | `0xc80c3d019e0b9e4c` | 0.756x | 0.655x |
| 8 | 141.262 us | 215.411 us | 3.2% | `0xd16df20a45d683c7` | 1.525x | 1.475x |
| 10 | 252.025 us | 213.670 us | 3.3% | `0x7d0941f1c8c5f9e8` | 0.848x | 0.820x |
| 12 | 486.945 us | 237.167 us | 2.9% | `0x7776688d262fc467` | 0.487x | 0.473x |
| 16 | 1.504 ms | 484.207 us | 1.4% | `0x5820b68b7d69021d` | 0.322x | 0.317x |

### Trend

Both ratios decline monotonically in the large: multiplication from 4.260x at
`n = 4` to 0.549x at `n = 20`, crossing 1 almost exactly at `n = 12`
(1.000x raw, 0.897x adjusted); inversion from 1.635x at `n = 4` to 0.322x at
`n = 16`. The two declines have different causes, and only one of them is a
statement about arithmetic.

For **multiplication** the decline is PARI's fixed per-call marshalling being
amortised, not an algorithmic-class difference. Fitting each side's growth
across the six rungs, with the 6.992 us driver floor subtracted from PARI:

- Hex grows as `n^2.01` — its declared `n^2` model, measured on the same
  inputs as the ladder.
- PARI's net cost grows as `n^0.86`, and its net times are 24.4, 33.9, 42.4,
  60.7, 79.3 and 97.3 us.

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

- Hex grows as `n^3.02`.
- PARI's net cost grows as `n^2.14`, with net times 25.8, 45.4, 208.4, 206.7,
  230.2 and 477.2 us.

This is a diverging trend, not a constant-factor gap, so it contradicts the
comparator's declared expectation. It is also independent corroboration of the
finding in §Concerns: the internal ladder measures `QAdjoin.inv` growing about
one power of `n` faster than its declared model, and the external comparator
measures it growing about one power of `n` faster than PARI's implementation
of the same operation on the same inputs. Two unrelated instruments agree, and
the mechanism — coefficient swell in the unnormalised rational extended gcd —
predicts exactly this. Recorded against
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
| `algebraic-poly-roots` | `runAlgebraicRootsLadder` n=6 | 5,652 / 8 | 0.778 ms | allocation 53.38%, GMP 31.86%, Lean runtime 12.03%, own code 0.65% | 97.93% |

The rejected counts are the untimed fixture preludes, which the filtering
postprocessor excludes by construction. `runQAdjoinMulLadder` rejects more
samples than it retains because building its certified root of `X^16 - 2`
costs 4.9 s against a 5 s timed region.

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
5.802 us `runAddEliminant` fixed case against a 46 s call, and 92% of the call
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
| 90.34% | `Hex.QAdjoin.roots?` |
| 90.32% | `Hex.QAdjoin.Roots.componentRoots?` |
| 89.47% | `Hex.isolate` / `isolateLoop` |
| 80.89% | `Hex.taylor` |

The same `QAdjoin.roots?` entry point, profiled on an input with a single
squarefree component, spends 90.32% in `componentRoots?` and never reaches
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
| [`bench-results/hex-number-field-phase4-comparators.json`](bench-results/hex-number-field-phase4-comparators.json) | `116c260cd`, clean tree | idle | `922cf24a2fa1072bcb6cf447f586ccf240b882e611366a8b46c83750be929f47` |

`066f6fc29` is the commit every ladder number was measured at. `a2b70b949`
differs from it only in two comments and `116c260cd` only by adding comparator
rungs, so neither changes the compiled code any ladder measurement used; the
five profiles were taken from the `066f6fc29` binary. Toolchain throughout:
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
  `beta = +0.887` with monotone `C` and spreads of 2.6% to 8.7% at the rungs
  carrying the signal, and the shipped `DensePoly.xgcdLeft` chain's rational
  entries reach `Θ(n²)` bits against the `Θ(n log n)` Hadamard bound a
  normalised chain attains.
  https://github.com/kim-em/hex-dev/issues/9721 — bench-found: QAdjoin.inv's
  rational extended gcd swells coefficients to Theta(n^2) bits.
- **The advertised API surface is not fully registered.** Roughly thirty
  advertised compiled operations have no `setup_benchmark` or
  `setup_fixed_benchmark`, and `Roots.normEliminant` and `Roots.evalEliminant`
  are separable asymptotically significant phases of `QAdjoin.roots?` that
  nothing measures, so the Attribution rule is not satisfied.
  https://github.com/kim-em/hex-dev/issues/9722 — audit-found: HexNumberField's
  advertised API surface is not fully registered for Phase 4.
- **`QAdjoin.roots?` is slower than its declared isolation ceiling.**
  `runQAdjoinRootsLadder` gives a monotone smooth-log slope of `+0.641` with
  spreads at or below 2%; the derivation's claim that norm-eliminant isolation
  dominates the double resultant is untested because neither phase is
  registered.
  https://github.com/kim-em/hex-dev/issues/9724 — bench-found: QAdjoin.roots?
  is slower than its declared isolation model by ~n^0.64.
- **Two ladders declare envelopes their input families cannot realise.**
  `runExactLadder` runs `n^4.21` against a BHKS `n^9` envelope because
  `(X^n - 2)(X + 3)` makes recombination free, and
  `runAlgebraicRootsLadder` carries the linear common-field prelude at its low
  rungs. Both return the faster-than-declared direction.
  https://github.com/kim-em/hex-dev/issues/9725 — audit-found: the
  exactification and algebraic-root ladders declare envelopes their input
  families cannot realise.
