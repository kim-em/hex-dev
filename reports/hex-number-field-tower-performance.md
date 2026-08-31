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
It registers 4 controlled parametric targets and 36 fixed targets (40 total).
The adjacent comments in the driver derive each model from the work performed
inside the timed function; the models below are copied from the registration
sites.

| target | operation and controlled input | declared model |
|---|---|---|
| `runTowerAddLadder` | coordinate addition in the height-two tower `ℚ(√2, 3^(1/n))` at dimension `D = 2n`, both operands dense and all-nonzero | `n` |
| `runTowerMulLadder` | schoolbook tower multiplication and recursive top-down reduction at dimension `D = 2n` | `n * n` |
| `runTowerInvLadder` | recursive extended-gcd inversion in the top quotient over the fixed quadratic base | `n * n * (Nat.log2 (n + 2) + 1)` |
| `runTowerFactorLadder` | Trager factorization over `ℚ(√2)` of the degree-`n` Selmer trinomial `X^n - X - 1` | `tragerLadderModel n` |

`tragerLadderModel` writes out the SPEC's worst-case Trager recurrence at
`d = deg m_α = 2` and component degree `m = n`: the shift-count bound
`tragerShiftCount(d, m) = choose(d * m, 2) + 1 = choose(2n, 2) + 1` one-level
norms, each an `O(n^2)`-operation Brown resultant against the quadratic
relation, plus the recursive rational factorization of the accepted
degree-`2n` norm at its classical BHKS bound, the dominant term:

```lean
def tragerLadderModel (n : Nat) : Nat :=
  let bigN := 2 * n
  (bigN * (bigN - 1) / 2 + 1) * (n * n)
    + bigN ^ 9 + bigN ^ 7 * (Nat.log2 (bigN + 2)) ^ 2
```

This is deliberately a conservative worst-case envelope, not a prediction of
the deterministic family's realised cost; §Verdicts reads the measurement
against it in that light.

The 36 fixed registrations are 23 Lean component cases covering the SPEC's
Phase-4 components (`runOfQAdjoin`, `runAdd`, `runSub`, `runNeg`, `runMul`,
`runInv`, `runDiv`, `runSMul`, `runAdjoin`, `runAdjoinIdentity`,
`runOneLevelNorm`, `runShiftSearch`, `runFactorRat`, `runFactorRetry`,
`runFactorRecursive`, `runCheckFactorization`, `runSplit`, `runFlatten`,
`runBasisImages`, `runCertifies`, `runCoordinateMaps`, `runRecoverPair`,
`runRecoverSearch`), twelve Lean/PARI comparator rungs
(`runTowerFactorPair{2,3,4,6,8,12}` / `runPariNfFactor{2,3,4,6,8,12}`), and
one external-driver overhead probe (`runPariNfFactorOverhead`). Every fixed
registration declares an `expectedHash`.

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

The Trager ladder's Selmer trinomials `X^n - X - 1` (irreducible over `ℚ`
for every `n ≥ 2`, and over `ℚ(√2)` because their Galois group leaves the
root field without quadratic subfields) have rational coefficients, so the
shift-zero one-level norm is the square `f²` and the bounded shift search
always performs a genuine retry before accepting a squarefree norm. The same
coefficient array feeds the PARI comparator requests, so both sides factor
the identical input. Every fixture in this library is deterministic; no
registration draws from a random seed.

### Scientific ranges

The addition and inversion ladders run at `n = 1, 2, 3, 4, 6` (dimension 2
through 12), the range the library's merge-facing conformance bound (tower
dimension at most 8, plus the dimension-12 asymptotic rung) makes meaningful.
The multiplication schedule extends through `n = 8, 12` because its
normalized cost has a small-dimension transient (per-element construction and
the `O(D)` checksum walk weigh more against `D²` work at dimension four) that
flattens from `n = 6` on; the short schedule ended inside the transient and
produced a spurious `+0.17` residual against the quadratic model. The raised
per-call cap accommodates the untimed tower construction at `m = 8` and
`m = 12` in prep (its `adjoin?` factors `X^m - 3` over `ℚ(√2)` outside the
timed region). The Trager schedule extends to
`n = 2, 3, 4, 6, 8, 12, 16, 24` (norm degrees 4 through 48) so the family's
local exponents are readable across three and a half octaves; its top rung
times a 253 ms call against a 120 s cap.

All four parametric registrations set `signalFloorMultiplier := 1.0`. The
justification tracks `SPEC/benchmarking.md` §Spawn-floor filter: every rung
uses warm child-side inner repeats auto-tuned to the 100 ms
`targetInnerNanos` floor, so each child-side timed batch is at least 100 ms
against a measured 40.4 to 41.4 ms per-spawn floor, while the conservative
default 10x multiplier would demand 400 ms batches and discard rungs without
changing what is measured. JSON exports record `spawn_floor_nanos` alongside
every row.

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

A full `lake exe hexnumberfieldtower_bench verify` of all 40 registrations,
including the PARI pairs through the persistent driver, completes locally in
28.7 s against CI's repo-wide hard cap, under the 30 s per-library soft
warning. The cost is dominated by `runRecoverSearch`, whose smallest honest
input (the degree-six recovery adversary) takes about 21 s per call plus a
6 s fixture exactification; the remaining 39 registrations verify in about
2 s combined.

## Verdicts

All measurements below follow the shared-host protocol: the logical CPU was
preregistered as **CPU 13** (SMT sibling 61), verified idle immediately
before each run by differencing `/proc/stat` over a 3 s window (worst
observed: 2.3% busy on CPU 13, 0.7% on CPU 61) with `ps -eo pid,psr`
confirming only kernel threads resident, and every bench invocation pinned
with `taskset -c 13`. One-minute load average during the measurement windows
was between 2.3 and 2.9 on 96 logical CPUs. `scripts/bench/idle_core.py` was
consulted before pinning so concurrent measurements could not collide on the
preregistered core.

Three exports carry the parametric evidence:

```sh
taskset -c 13 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerFactorLadder \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json
taskset -c 13 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerAddLadder \
  Hex.NumberTowerBench.runTowerInvLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-scientific-arith-7d6c0c50-chungus2-cpu13.json
taskset -c 13 .lake/build/bin/hexnumberfieldtower_bench run \
  Hex.NumberTowerBench.runTowerMulLadder \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-number-field-tower-phase4-scientific-mul-7d6c0c50-chungus2-cpu13.json
```

| target | ladder | verdict | fitted slope | cMin..cMax | worst spread |
|---|---|---|---:|---|---:|
| `runTowerAddLadder` | 1, 2, 3, 4, 6 | **consistent** | -0.082 | 222.4..240.8 | 8.40% |
| `runTowerMulLadder` | 1, 2, 3, 4, 6, 8, 12 | **consistent** | +0.080 | 3653.5..4085.3 | 20.30% |
| `runTowerInvLadder` | 1, 2, 3, 4, 6 | **consistent** | -0.029 | 8324.9..9583.4 | 3.66% |
| `runTowerFactorLadder` | 2, 3, 4, 6, 8, 12, 16, 24 | inconclusive, faster | -6.506 | 0.000..0.110 | 7.81% |

Representative medians: addition 1.335 µs at `n = 6` (dimension 12);
multiplication 588.3 µs at `n = 12` (dimension 24); inversion 1.199 ms at
`n = 6`; Trager factorization 253.0 ms at `n = 24` (norm degree 48). Result
hashes agree across every trial at every rung in all three exports.

The three arithmetic ladders fit their declared models. The multiplication
fit spans `n = 2..12` after the harness's warmup trim drops `n = 1`; its
normalized cost climbs 3251 to 4085 across the transient and is flat from
`n = 6` on (4064 at `n = 8`, 4128 at `n = 12` in the pre-registration probe;
4060 and 4085 in the committed export), which is what the extended schedule
was added to expose. Its 20.30% worst spread is one outlier trial at
`n = 4` (72.98 µs against four trials within 1.2% of 61.0 µs); the median is
unaffected. Addition's 8.40% worst spread is likewise a single 766 ns trial
at `n = 3`.

`runTowerFactorLadder` reports `inconclusive: looks faster than declared by
~n^6.5`, and that is the expected direction, the same reading the merged
HexBerlekampZassenhaus report records for its deliberately conservative
envelope models: observed cost growing strictly more slowly than a worst-case
envelope is not a defect finding, and no ladder shows the slower-than-declared
direction. Two mechanisms account for the gap, both visible in the data:

- **Realised shift count.** The model charges the SPEC's proof-driven bound
  `tragerShiftCount(2, n) = choose(2n, 2) + 1` one-level norms; the
  deterministic Selmer family realises the mandatory retry (the repeated
  shift-zero norm) and then accepts the first squarefree shifted norm, so the
  realised count stays a small constant while the charged count grows as
  `O(n²)`.
- **BHKS envelope versus realised base factorization.** The model's dominant
  `(2n)^9` term is the classical worst-case bound for rationally factoring
  the accepted degree-`2n` norm; the §Profile capture at `n = 16` shows the
  actual Berlekamp-Zassenhaus call (`Hex.ZPoly.factorize`) at 5.26% of the
  timed call, with the measured cost concentrated in rational-polynomial gcd
  and resultant machinery instead.

The measured curve is informative about where the real asymptotics live: the
local exponent between successive rungs climbs monotonically, 0.80 (2 to 3),
1.27, 1.38, 1.88, 2.48, 3.23, and 4.48 (16 to 24), so the
coefficient-growth-driven phases are becoming dominant well inside the
measured range while remaining far below the envelope's ~n^9 top-rung
behaviour. The envelope is not contradicted at any rung.

### Fixed registrations

Export (all 23 Lean component cases, clean `3f23d6425`):

```sh
taskset -c 13 .lake/build/bin/hexnumberfieldtower_bench run \
  <the 23 Lean fixed targets> \
  --export-file reports/bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json
```

All 23 observed hashes match their `expectedHash` declarations and agree
across repeats.

| fixed target | median | fixed target | median |
|---|---:|---|---:|
| `runOfQAdjoin` | 504 ns | `runFactorRat` | 73.6 µs |
| `runAdd` | 511 ns | `runFactorRetry` | 823.5 µs |
| `runSub` | 516 ns | `runFactorRecursive` | 7.632 ms |
| `runNeg` | 654 ns | `runCheckFactorization` | 23.9 µs |
| `runSMul` | 1.070 µs | `runSplit` | 78.32 ms |
| `runMul` | 13.03 µs | `runFlatten` | 37.56 ms |
| `runInv` | 64.31 µs | `runBasisImages` | 25.5 µs |
| `runDiv` | 76.81 µs | `runCertifies` | 239.7 µs |
| `runOneLevelNorm` | 34.1 µs | `runCoordinateMaps` | 173.2 µs |
| `runShiftSearch` | 127.2 µs | `runRecoverPair` | 337.3 µs |
| `runAdjoin` | 920.2 ms | `runRecoverSearch` | 20.84 s |
| `runAdjoinIdentity` | 23.43 ms | | |

The component decomposition reads as the SPEC intends. In the dimension-four
tower, the linear-cost surface (add, sub, neg, scalar action) sits at 0.5 to
1.1 µs, quadratic multiplication at 13 µs, recursive inversion at 64 µs, and
division at 77 µs, consistent with inversion dominating one multiplication.
On the factorization side, one one-level norm is 34 µs, the retry-exercising
shift search 127 µs (roughly two norms plus squarefreeness checks, as
derived), the rational base case 74 µs, the one-level retry case 823 µs, and
the recursive dimension-four case 7.6 ms; checked replay of a precomputed
factorization is 24 µs. Flattening decomposes into a 25.5 µs basis-image
expansion, 240 µs certification, 173 µs coordinate maps, and a 337 µs
fast-recovery gcd rejection, against 37.6 ms for the full two-level
`flatten?`. The two deliberate heavyweights are `runAdjoin` (920 ms: adjoining
a fourth root of two spends its time in fixed-embedding factor selection, see
§Profile) and `runRecoverSearch` (20.8 s: the degree-six recovery adversary
pays a full rejected candidate before accepting shift `-1`).

## Comparator ratios

The library SPEC declares one external comparator,
**PARI/GP nffactor via cypari2**, class `informational`, scoped to the
`factor?` bench targets.
`nffactor(nfinit f, t)` is the callable PARI unit surface for factoring a
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
4.34.0-rc2, LeanBench 0.1.0, binary built from clean `d9fc6d73f` (identical
compiled algorithm code to the export commits; the later `3f23d6425` changed
only fixed-registration `where` configuration). Every fixture is
deterministic and no runtime oracle participates in any profiled route. The
parametric representatives ran through the lean-bench-samply orchestrator
with timed-region filtering:

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerMulLadder    12 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerInvLadder     6 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexnumberfieldtower_bench \
  Hex.NumberTowerBench.runTowerFactorLadder 16 5000000000
```

Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexnumberfieldtower_bench`.
Raw filtered `*.json.gz` artefacts stay developer-local under `/tmp` as
`SPEC/profiling.md` requires; the committed summaries artefact is listed in
§Artefact traceability.

The lean-bench child emits no timed-region sidecar for fixed dispatch, so
the orchestrator cannot capture fixed registrations; this is the same
scope condition the merged HexBerlekampZassenhaus report records for its
fixed-only family. The two fixed-only families (`adjoin-extend`,
`split-flatten`) are therefore covered by whole-bench-thread raw samply
captures of the fixed-mode child over a long auto-tuned batch
(`_child --bench <case> --fixed --min-total-nanos 5000000000`), analysed
with the same categorizer. In each raw capture the registered case's own
frame carries 95.7% or more of the thread's samples (95.71% for
`runAdjoin`, 99.90% for `runSplit`, 97.93% for `runFlatten`), so process
init and one-shot fixture construction contribute under 5% and the shape
conclusions below do not depend on the missing filter; these captures carry
no lean-bench-samply calibration/sensitivity diagnostics, which is the
declared scope of profile coverage for those two families, not an omission.

| family | case | retained / rejected | calibration residual | leaf cost | classified |
|---|---|---:|---:|---|---:|
| `tower-coordinate-arithmetic` | `runTowerMulLadder` n=12 | 4,957 / 237,605 | 0.700 ms | allocation 39.72%, Lean runtime 31.07%, GMP 23.56%, own code 4.80% | 99.15% |
| `tower-coordinate-arithmetic` | `runTowerInvLadder` n=6 | 4,943 / 2,854 | 0.542 ms | GMP 43.19%, allocation 34.86%, Lean runtime 19.97%, own code 1.60% | 99.62% |
| `trager-factorization` | `runTowerFactorLadder` n=16 | 5,342 / 7 | 0.724 ms | GMP 54.02%, Lean runtime 24.35%, allocation 19.17%, own code 2.23% | 99.78% |
| `adjoin-extend` | `runAdjoin` (raw fixed capture) | 13,786 / n.a. | n.a. | allocation 46.44%, GMP 27.26%, Lean runtime 24.05%, own code 2.01% | 99.75% |
| `split-flatten` | `runSplit` (raw fixed capture) | 9,985 / n.a. | n.a. | Lean runtime 40.01%, allocation 37.91%, GMP 13.52%, own code 7.83% | 99.27% |
| `split-flatten` | `runFlatten` (raw fixed capture) | 18,762 / n.a. | n.a. | allocation 37.74%, Lean runtime 37.06%, GMP 20.47%, own code 4.47% | 99.74% |

The three filtered captures pass calibration (residuals 0.54 to 0.72 ms
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

84.37% of retained samples are inside `Hex.NumberTower.factor?`
(`factorSquarefree?` 81.60%); the remainder is harness and checksum
scaffolding outside the Hex namespace. Within the call:
`Hex.DensePoly.gcdAuxImpl` 54.08%, the replay/irreducibility certificate
`Factor.check`/`Factor.isIrreducible` 41.39%/41.20%, the bounded shift
search `Norm.findSquarefreeShiftAux` 40.72% with `Norm.isSquarefree` 25.95%,
the rational base case `Factor.factorRat?` 28.83%, resultant machinery
(`DensePoly.resultantOrdered` 10.88%), gcd recovery (`Factor.recover`
10.20%), and the actual integer factorization `Hex.ZPoly.factorize` at
5.26% (Hensel lift 2.55%, Berlekamp kernel 1.87%). Every named phase has a
registered component case (`runOneLevelNorm`, `runShiftSearch`,
`runFactorRat`, `runCheckFactorization`, and the ladder itself), and the
underlying `DensePoly` gcd/resultant kernels carry their own asymptotic
evidence in the upstream HexPoly/HexResultant reports. The 41% certificate
share is the executable checked-replay guarantee the SPEC mandates
(`Factorization.checked`); it is a deliberate structural cost, and it is
half the reason the BHKS-dominated envelope over-predicts (§Verdicts).

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
| [`bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-scientific-factor-7d6c0c50-chungus2-cpu13.json) | clean `7d6c0c50a` | idle, CPU 13 | `c0ae3da96fe41f36a87ed6665bf98cd1b2d4c9c209b541a7a0516cbdb28f9d30` |
| [`bench-results/hex-number-field-tower-phase4-scientific-arith-7d6c0c50-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-scientific-arith-7d6c0c50-chungus2-cpu13.json) | clean `027f4f033` (identical bench sources to `7d6c0c50a`) | idle, CPU 13 | `01e8cd69ef48d6fd903532dc7844475e1a4b6a3e89953c2c5646d67ef24138cf` |
| [`bench-results/hex-number-field-tower-phase4-scientific-mul-7d6c0c50-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-scientific-mul-7d6c0c50-chungus2-cpu13.json) | clean `d9fc6d73f` (identical bench sources to `7d6c0c50a`) | idle, CPU 13 | `e2aaeb97cc186923c21061f3733d897cbf02668fc26c92459025f96a5c049f40` |
| [`bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-fixed-3f23d642-chungus2-cpu13.json) | clean `3f23d6425` | idle, CPU 13 | `1927e8268c5ac22a1df0e987db5dff878e7ccdcc448252d21b6ee6240689f156` |
| [`bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json`](bench-results/hex-number-field-tower-phase4-comparators-3f23d642-chungus2-cpu13.json) | clean `322f53b15` (identical bench sources to `3f23d6425`) | idle, CPU 13 | `5c60e35f20265683fff0eb01f397e3355957fcd0737f0ca21e7781a0b30f0a3f` |
| [`bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json`](bench-results/hex-number-field-tower-profile-summaries-d9fc6d73-chungus2.json) | binary from clean `d9fc6d73f` | unpinned (shape capture) | `31767bff125621d07391e151bc613a3a1c8ee7b74300a81fd7029af2198b505c` |

The bench-source history inside this evidence set: `aa6151400` added the
PARI driver overhead probe; `bc3778b79` fixed the bounded-height ladder
fixture and extended the multiplication schedule; `7d6c0c50a` extended the
Trager schedule and added the `n = 8, 12` comparator pairs; `3f23d6425`
moved lazily built fixtures out of the fixed timed regions and completed the
`expectedHash` coverage. Artifact-only commits between them change no bench
source. Toolchain throughout: Lean 4.34.0-rc2 (`leanprover/lean4:v4.34.0-rc2`),
LeanBench 0.1.0, samply 0.13.1, PARI 2.17.2 driven by cypari2 2.2.4 through
`scripts/oracle/pari_bench_driver.py` (Python from `HEX_PARI_BENCH_PYTHON`).
Host throughout: `chungus2`, Linux x86-64 6.12.100, AMD EPYC 9455 48-Core
Processor, 96 logical CPUs, measurements pinned to preregistered CPU 13.

## Concerns

- [#9815](https://github.com/kim-em/hex-dev/issues/9815) tracks the failing
  Trager envelope and the fixed component registrations' missing ordered-mode
  evidence.

The measurement defects surfaced while producing this evidence (the
height-varying ladder fixture, the multiplication schedule ending inside its
small-dimension transient, and fixed cases timing their lazily built
fixtures) were repaired in the bench commits named in §Artefact traceability
and every number above postdates the repairs; they are historical and resolved.
