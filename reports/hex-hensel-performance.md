# HexHensel Performance Report

## Bench Targets

- `Hex.HenselBench.runModPChecksum`: `n`
- `Hex.HenselBench.runLiftToZChecksum`: `n`
- `Hex.HenselBench.runReduceModPowChecksum`: `n`
- `Hex.HenselBench.runLinearHenselStepChecksum`: `n * n`
- `Hex.HenselBench.runHenselLiftChecksum`: `liftLinearComplexity param = n * n * k`
- `Hex.HenselBench.runQuadraticHenselStepChecksum`: `n * n`
- `Hex.HenselBench.runPolyProductChecksum`: `n * n`
- `Hex.HenselBench.runMultifactorLiftChecksum`: `liftLinearComplexity param = n * n * k`
- `Hex.HenselBench.runMultifactorLiftQuadraticChecksum`: `liftQuadraticComplexity param = n * n * Nat.log2 (k + 1)`

## Verdicts

Scientific run at commit `24a4fcaa9dbe` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexhensel_bench run \
    Hex.HenselBench.runModPChecksum \
    Hex.HenselBench.runLiftToZChecksum \
    Hex.HenselBench.runReduceModPowChecksum \
    Hex.HenselBench.runLinearHenselStepChecksum \
    Hex.HenselBench.runHenselLiftChecksum \
    Hex.HenselBench.runQuadraticHenselStepChecksum \
    Hex.HenselBench.runPolyProductChecksum \
    Hex.HenselBench.runMultifactorLiftChecksum \
    Hex.HenselBench.runMultifactorLiftQuadraticChecksum \
    --export-file reports/bench-results/hex-hensel-24a4fca.json
```

The run uses the deterministic dense `F_5`/`Z[x]` benchmark fixtures
constructed in `HexHensel/Bench.lean` (small prime `p = 5` throughout);
no random seeds are involved. The harness recorded `24a4fca-dirty`
because this worktree carried an unrelated pre-existing
`.claude/CLAUDE.md` modification and untracked `.claude/` content.
Export artefact: `reports/bench-results/hex-hensel-24a4fca.json`,
SHA-256 `4633cdcaed2f7d0b056c7eb7b754258c9997f6360427b5a8d28b421e5ae53b49`.

- `Hex.HenselBench.runModPChecksum`: consistent with declared
  complexity (`cMin=108.877, cMax=111.783, β=+0.010`,
  parameters `8192..131072`, final hash `0x93df396c13011785`).
- `Hex.HenselBench.runLiftToZChecksum`: consistent with declared
  complexity (`cMin=53.849, cMax=54.183, β=−0.002`,
  parameters `8192..131072`, final hash `0x389d28873eb4eb88`).
- `Hex.HenselBench.runReduceModPowChecksum`: consistent with declared
  complexity (`cMin=117.236, cMax=117.706, β=−0.001`,
  parameters `8192..131072`, final hash `0x2bb1d2338fde61ab`).
- `Hex.HenselBench.runLinearHenselStepChecksum`: consistent with
  declared complexity (`cMin=314.076, cMax=331.408, β=−0.031`,
  parameters `64..512`, final hash `0x660394e9aae087cc`).
- `Hex.HenselBench.runHenselLiftChecksum`: consistent with declared
  complexity (`cMin=320.073, cMax=396.792, β=−0.096`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xf4ac4cfd1b7bc4db`).
- `Hex.HenselBench.runQuadraticHenselStepChecksum`: consistent with
  declared complexity (`cMin=1285.400, cMax=1382.515, β=+0.023`,
  parameters `64..512`, final hash `0x13f3af080ce8ac5e`).
- `Hex.HenselBench.runPolyProductChecksum`: consistent with declared
  complexity (`cMin=222.696, cMax=258.113, β=+0.079`,
  parameters `128..1024`, final hash `0x3a54a0eb632efee0`).
- `Hex.HenselBench.runMultifactorLiftChecksum`: consistent with
  declared complexity (`cMin=318.608, cMax=396.946, β=−0.116`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xe09bda79cfa1f787`).
- `Hex.HenselBench.runMultifactorLiftQuadraticChecksum`: consistent
  with declared complexity (`cMin=1171.755, cMax=1976.812, β=−0.037`,
  parameters `32_004..192_064` (encoded `(n, k)`), final hash
  `0xe09bda79cfa1f787`).

Smoke wiring was also checked at the same commit with:

```sh
lake exe hexhensel_bench list
lake exe hexhensel_bench verify
```

`verify` passed all nine registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-hensel.md §"External comparators"` names
`FLINT nmod_poly_hensel_lift_* via python-flint` (matching
`libraries.yml: HexHensel.phase4.comparators[0].tool`) as the
`informational` external comparator for HexHensel, scoped to bench
targets exercising single-step and iterated Hensel lifting of factor
pairs over `Z_{p^k}`. The comparator is wired through
`Hex.BenchOracle.Flint.runOp` against the shared persistent-subprocess
python-flint driver (`scripts/oracle/flint_bench_driver.py`, HO-20),
which the driver exposes as the `nmod_poly_hensel` family with
`lift_once` (single Newton-style doubling step) and `lift` (iterated
to a target exponent). The five `setup_benchmark` registrations
exercising Hensel-lift work, paired with their FLINT comparator, are:
`runLinearHenselStepChecksum` ↔ `nmod_poly_hensel.lift_once` at `k = 1`,
`runHenselLiftChecksum` ↔ `nmod_poly_hensel.lift` to `target_k = input.k`,
`runQuadraticHenselStepChecksum` ↔ `nmod_poly_hensel.lift_once` at
`k = 1` (Bezout pair computed inside the driver, mirroring the Hex
seed-from-`(0, 1)` setup work),
`runMultifactorLiftChecksum` ↔ `nmod_poly_hensel.lift` on the
two-factor fixture, and
`runMultifactorLiftQuadraticChecksum` ↔ the same `nmod_poly_hensel.lift`
call (both Hex multifactor strategies reach the same lifted
factorisation `mod p^k` on the shared fixture). The remaining
`setup_benchmark` registrations (`runModPChecksum`,
`runLiftToZChecksum`, `runReduceModPowChecksum`, `runPolyProductChecksum`)
are bridge operations and ordered linear products, not Hensel-lift
work, and so have no `nmod_poly_hensel_lift_*` pairing per the SPEC
scope.

Hex normalises lifted factors to non-negative residues in `[0, p^k)`
via `reduceModPow`; the python driver returns centred residues in
`(-p^k/2, p^k/2]`. The two checksum streams therefore diverge by
representation choice — each is internally stable across repeats, but
they are not expected to match each other.

### Per-call overhead

FLINT per-call overhead is measured by timing one driver spawn plus
one trivial `fmpz_mat.det` request (`/tmp/flint-overhead-measure.py`,
11 spawns on the same host): median **65.8 ms**, min 60.6 ms. The
`setup_fixed_benchmark` shape spawns one bench child per repeat, so
every FLINT median below includes one driver startup. The `adjusted
ratio` column subtracts this overhead from the FLINT median when
positive, then divides by the Hex median; the value is reported as
`0` when the FLINT median is below the overhead floor. A rung is
**eligible** under `SPEC/benchmarking.md §"Headline reports"
§"Comparator ratios"` when (a) the 65.8 ms overhead is at most 50%
of measured FLINT wall time on that rung and (b) per-call wall time
is at most the 10 s hard ceiling.

### Driver coverage limit

The python driver implements `nmod_poly_hensel.lift_once` and `lift`
via `fmpz_poly` arithmetic because python-flint does not bind the
`nmod_poly_hensel_lift_*` C entry points directly. Each Newton step
doubles the coefficient modulus, so `fmpz_poly` operand magnitudes
grow rapidly: empirical measurement on this host shows the driver
process consuming about 540 MB at `(n = 32, target_k = 16)`,
> 12 GB at `(n = 128, target_k = 16)`, and > 20 GB at
`(n = 192, target_k = 16)`. The Hex parametric `runHenselLiftChecksum`
schedule runs to `(n = 192, target_k = 64)` because Hex's
`reduceModPow` bounds coefficients to `[0, 5^k)` directly in Lean
without the python-side `fmpz_poly` intermediates; that depth is not
reachable with the current driver implementation. The six paired
rungs for the iterative lifters (`HenselLift`, `MultiLift`,
`MultiLiftQ`) therefore sit at `k = 8` with `n` varying so the
algorithmic trend across `n` is visible against the per-call FLINT
floor.

### Scientific run command

Comparator ratios were recorded at commit `77870fc-dirty` on
`carica` (Apple M2 Ultra, macOS 14.6.1) with five `lake exe
hexhensel_bench run` invocations, one per Hex Hensel-lift surface,
each pairing the six Hex `setup_fixed_benchmark` rungs with their
matching FLINT comparator. The `-dirty` flag reflects pre-existing
`.claude/CLAUDE.md` modifications and untracked `.claude/`
session-local content in this worktree, unrelated to the bench
targets themselves. Export artefacts:

- `reports/bench-results/hex-hensel-linear-flint.json`, SHA-256
  `5e941a5dd69d15417cf92bfeea1d5427e6d241fb91d1fb7ed4812bc29f834e9a`.
- `reports/bench-results/hex-hensel-quadratic-flint.json`, SHA-256
  `8c4e4b9b6e80f4fbe77bdaf3bcc1768be970bfec95baa1ec08826ce661060d39`.
- `reports/bench-results/hex-hensel-iterated-linear-flint.json`, SHA-256
  `0204005fd5bf12a520ee94e9208c74cb3063b4e4672d393ad700368d9b79f9d6`.
- `reports/bench-results/hex-hensel-multilift-flint.json`, SHA-256
  `7a769515dda09b8656c75d2aa8fca248800c0fc07693b88a043864ba5fcc2c7b`.
- `reports/bench-results/hex-hensel-multiliftq-flint.json`, SHA-256
  `940442b0d5b1a4f89aa362994334ea3514473b5d58b2bb444f89983357b3791b`.

### FLINT `nmod_poly_hensel.lift_once` vs `runLinearHenselStepChecksum`

Input family `linear-hensel`, single Newton step from `mod 5` to
`mod 5^2` on the deterministic dense two-factor fixture (`g = x + 4`
from `linearZFactor 59`, `h = denseZPoly (n + 1) 62`,
`f = g*h + 5 * denseZPoly (n + 1) 67`, Bezout `(s, t) =
normalizedXGCD 5 g h`).

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 64  | 1.573 ms  | 58.170 ms | 36.98x | 0.000x | no |
| 128 | 5.723 ms  | 58.717 ms | 10.26x | 0.000x | no |
| 192 | 12.385 ms | 56.465 ms |  4.56x | 0.000x | no |
| 256 | 21.936 ms | 57.258 ms |  2.61x | 0.000x | no |
| 384 | 47.772 ms | 68.311 ms |  1.43x | 0.054x | no |
| 512 | 83.342 ms | 68.861 ms |  0.83x | 0.037x | no |

Trend: no rung is eligible — FLINT's wall time sits at the
driver-spawn floor (~57–68 ms) at every measured `n`, so the overhead
is more than half of the measured FLINT call. The adjusted ratios at
the top of the ladder converge to about `0.04x`, meaning FLINT's
algorithmic time for a single Newton step is under 5 ms even at
`n = 512`, while Hex's `linearHenselStep` spends 83 ms there. This is
the canonical `SPEC/benchmarking.md §"Comparator process overhead
reported as algorithmic difference"` anti-pattern, recorded in
adjusted form rather than as a raw verdict; the comparator is
`informational`, so no gating-goal verdict is required.

### FLINT `nmod_poly_hensel.lift_once` vs `runQuadraticHenselStepChecksum`

Input family `quadratic-hensel`, single Newton step from `mod 5` to
`mod 5^2`. `n = 128` is replaced with `n = 160` because the
`QuadraticInput` fixture at `n = 128` has `gcd(g, h) ≠ 1 (mod 5)`,
which fails the FLINT driver's Bezout precondition.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 64  |   5.955 ms | 61.139 ms | 10.27x | 0.000x | no |
| 160 |  35.218 ms | 61.129 ms |  1.74x | 0.000x | no |
| 192 |  50.664 ms | 62.826 ms |  1.24x | 0.000x | no |
| 256 |  86.545 ms | 64.320 ms |  0.74x | 0.000x | no |
| 384 | 200.198 ms | 62.516 ms |  0.31x | 0.000x | no |
| 512 | 354.758 ms | 62.245 ms |  0.18x | 0.000x | no |

Trend: no rung is eligible — FLINT's wall time stays at the
driver-spawn floor across the entire schedule, so the comparator
exposes nothing of FLINT's algorithmic time. The raw ratios fall
below 1.0 from `n = 256` onward, recorded as a Concern below: Hex's
`quadraticHenselStep` spends 355 ms at `n = 512` while FLINT's
single-step lift, with internal Bezout, returns in 62 ms total.
Subtracting the driver overhead pins FLINT's algorithmic time at
< 5 ms even at `n = 512`, so the Hex surface is doing about 70× the
algorithmic work of FLINT's tuned single-step lift.

### FLINT `nmod_poly_hensel.lift` vs `runHenselLiftChecksum`

Input family `linear-hensel`, iterated lift from `mod 5` to `mod 5^8`
on the deterministic dense two-factor fixture. Hex performs 8 linear
correction steps; FLINT reaches the same final modulus via
`⌈log₂ 8⌉ = 3` quadratic doublings.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 32  |   2.798 ms |  64.390 ms | 23.01x | 0.000x | no |
| 64  |  10.046 ms |  70.264 ms |  6.99x | 0.449x | no |
| 96  |  21.634 ms |  82.150 ms |  3.80x | 0.758x | no |
| 128 |  37.504 ms | 101.153 ms |  2.70x | 0.944x | no |
| 192 |  83.645 ms | 127.723 ms |  1.53x | 0.741x | no |
| 256 | 146.079 ms | 538.991 ms |  3.69x | 3.239x | yes |

Trend: raw ratios fall as `n` grows out of the driver-floor regime,
then jump back up at `n = 256` where FLINT's algorithmic time finally
exceeds the spawn floor. The one eligible rung records FLINT at
3.24× Hex's wall time on the same lift. The python-emulated lift
allocates rapidly growing `fmpz_poly` intermediates per Newton step,
so the per-call cost compounds super-linearly in `n` once coefficient
operands cross the `fmpz_poly` Karatsuba/FFT threshold.

### FLINT `nmod_poly_hensel.lift` vs `runMultifactorLiftChecksum`

Input family `multifactor-lifting`, iterated two-factor lift from
`mod 5` to `mod 5^8` on the production multifactor fixture
(`factors = #[g, h]`).

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 32  |   2.821 ms |  71.918 ms | 25.49x | 2.187x | no |
| 64  |   9.998 ms |  69.811 ms |  6.98x | 0.406x | no |
| 96  |  21.858 ms |  81.682 ms |  3.74x | 0.729x | no |
| 128 |  37.683 ms | 104.190 ms |  2.77x | 1.020x | no |
| 192 |  83.333 ms | 129.744 ms |  1.56x | 0.768x | no |
| 256 | 146.336 ms | 622.740 ms |  4.26x | 3.806x | yes |

Trend: same shape as the iterated linear lift on its own fixture;
only `n = 256` is eligible and records FLINT 3.81× slower than Hex
on the comparable two-factor lift. The Hex multifactor wrapper
delegates each factor's lift to the linear single-step kernel, which
shares the bounded-coefficient `reduceModPow` representation, so the
two ladders read together.

### FLINT `nmod_poly_hensel.lift` vs `runMultifactorLiftQuadraticChecksum`

Same FLINT call as `runMultifactorLiftChecksum` — Hex's quadratic
multifactor strategy reaches the same lifted factorisation `mod 5^8`
on the same fixture; the ratio is reported separately so each Hex
strategy's wall time is visible against the shared FLINT reference.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 32  |   2.588 ms |  63.113 ms | 24.39x | 0.000x | no |
| 64  |   9.361 ms |  63.767 ms |  6.81x | 0.000x | no |
| 96  |  21.094 ms |  79.778 ms |  3.78x | 0.665x | no |
| 128 |  36.199 ms | 105.714 ms |  2.92x | 1.103x | no |
| 192 |  81.582 ms | 120.628 ms |  1.48x | 0.673x | no |
| 256 | 144.571 ms | 619.585 ms |  4.29x | 3.832x | yes |

Trend: same shape and same eligibility pattern as the linear
multifactor pairing. Hex's quadratic multifactor lifter consistently
edges its linear sibling on this fixture (Hex `MultiLiftQ` 144.6 ms
vs `MultiLift` 146.3 ms at `n = 256`), as expected from the
`log₂ k` vs `k` iteration counts; FLINT, going through a single
`lift` call that doubles internally regardless of which Hex sibling
it is paired with, records the same algorithmic ladder against both
Hex strategies.

## Profile

The profiles below were recorded with
`scripts/profile/run_profile.sh ./.lake/build/bin/hexhensel_bench
<target> <param> 5000000000` at commit `3bc24c50fbe5` on `carica`
(Apple M2 Ultra, macOS 14.6.1) at samply `0.13.1`'s 999 Hz sampling
rate. The bench binary reports `git_dirty=true` because this
worktree carries the pre-existing `.claude/CLAUDE.md` modification;
the report change does not touch benchmark code. The bench harness
reported `lean_bench_version=0.1.0`, toolchain
`leanprover/lean4:4.30.0-rc2`, target
`arm64-apple-darwin24.6.0`. All cases use deterministic fixtures and
no random seed.

The raw Firefox Profiler JSON artefacts are developer-local and are
not committed. Leaf and inclusive attribution below is computed from
the filtered samply JSON after retaining only the bench thread's
samples that fall inside LeanBench timed regions. Percentages are
sample-count shares of that filtered bench thread; the extra
`other Lean/library` bucket covers generated Lean/stdlib frames that
are neither Hex library code nor C-level `lean_*` runtime frames.

### `bridge-operations`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexhensel_bench \
    Hex.HenselBench.runReduceModPowChecksum 131072 5000000000
```

Representative case: deterministic dense degree-`131071` integer
polynomial with bounded `[-997, 997]`-magnitude coefficients reduced
through `Hex.ZPoly.reduceModPow _ 5 3`, parameter `n = 131072`, no
seed. Child row: `inner_repeats=256`,
`per_call_nanos=16757638.183594`, `result_hash=0x2bb1d2338fde61ab`.
Leaf samples were own Hex code 54.1%, GMP 14.3%, Lean runtime 11.0%,
other Lean/library code 7.0%, allocation/free 6.1%, and other 7.5%.
Inclusive own-code cost was led by `Hex.ZPoly.reduceModPow` (68.1%)
and `Hex.List.mapTR.loop.at...reduceModPow.spec` (62.2%), with
`Hex.DensePoly.trimTrailingZerosList → trimTrailingZeros → ofCoeffs`
accounting for the post-reduction normalisation (9.2%). The dominant
work maps to the registered
`runReduceModPowChecksum` target via
`ZPoly.reduceModPow → List.mapTR.loop → Int reduction mod 5^k`,
matching the `O(n)` cost model with one bounded reduction per
coefficient. The same code path serves the other two bridge
registrations (`runModPChecksum` and `runLiftToZChecksum`); their
verdicts come back consistent at the same parameter ladder, so a
single `bridge-operations` profile case suffices for the family.

Diagnostics:

```json
{
  "regions_total": 2,
  "total_timed_ms": 4307.56,
  "expected_samples_bench_thread": 4303.3,
  "retained_samples_bench_thread": 4206,
  "rejected_samples_bench_thread": 25,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142563061725000,
  "spawn_anchor_mono_ns": 330596981881541,
  "sidecar_mono_anchor_ns": 330598299522708,
  "samply_meta_start_time_ms": 1780142563070.2751
}
```

### `linear-hensel`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexhensel_bench \
    Hex.HenselBench.runLinearHenselStepChecksum 512 5000000000
```

Representative case: one linear Hensel correction over the
deterministic two-factor fixture (`g` a fixed degree-1 monic factor
`x + 4` from `linearZFactor 59`, `h` a deterministic dense
degree-`512` integer polynomial from `denseZPoly 513 62`,
`f = g*h + 5*e` with `e` a deterministic dense degree-`512`
perturbation from `denseZPoly 513 67`; Bezout pair `(s, t)` computed
fresh as `normalizedXGCD 5 g h` so that
`s * gMod + t * hMod ≡ 1 (mod 5)`) at parameter `n = 512`, no seed.
Child row: `inner_repeats=32`, `per_call_nanos=88824901.062500`,
`result_hash=0x660394e9aae087cc`. Leaf samples were own Hex code
49.1%, Lean runtime 23.4%, GMP 10.4%, allocation/free 6.5%, other
Lean/library code 1.6%, and other 9.0%. Inclusive own-code cost was
led by `Hex.DensePoly.mul` (98.5%), its inner multiplication loop
(88.1% / 71.2% stack entries), `Hex.ZMod64.mul` (66.5%), and
`Hex.ZPoly.linearHenselStep` (49.3%). The corrected fixture computes
both `s * eMod` and `q * hMod` as full F_5 polynomial
multiplications; the fixed degree-1 divmod by `gMod` remains a
smaller linear component. The dominant work maps to the registered
`runLinearHenselStepChecksum` target via
`linearHenselStep → DensePoly.mul (correction product) →
ZMod64.mul`, exactly as the `n²` cost model predicts for the two
dense F_5 correction products per step. The iterative wrapper
`runHenselLiftChecksum` shares this fixture and code path; with the
corrected Bezout pair its verdict comes back consistent over the
full encoded `(n, k)` ladder, so a single `linear-hensel` profile
case suffices for the family.

Diagnostics:

```json
{
  "regions_total": 2,
  "total_timed_ms": 2928.929916,
  "expected_samples_bench_thread": 2926.0,
  "retained_samples_bench_thread": 2923,
  "rejected_samples_bench_thread": 10,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142573530552000,
  "spawn_anchor_mono_ns": 330607450822833,
  "sidecar_mono_anchor_ns": 330607940118000,
  "samply_meta_start_time_ms": 1780142573538.2532
}
```

### `quadratic-hensel`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexhensel_bench \
    Hex.HenselBench.runQuadraticHenselStepChecksum 512 5000000000
```

Representative case: one quadratic Hensel correction (factor and
Bezout updates together, both lifted from `mod 5` to `mod 25`) over
the deterministic two-factor fixture (`g` a fixed degree-1 monic
factor, `h` a deterministic dense degree-`513` integer polynomial,
`f = g*h + 5*e`, Bezout pair seeded as `(s, t) = (0, 1)`) at
parameter `n = 512`, no seed. Child row: `inner_repeats=8`,
`per_call_nanos=383813703.125000`,
`result_hash=0x13f3af080ce8ac5e`. Leaf samples were own Hex code
48.5%, Lean runtime 18.1%, GMP 10.0%, allocation/free 8.0%, other
Lean/library code 6.9%, and other 8.5%. Inclusive own-code cost was
led by `Hex.ZPoly.quadraticHenselStep` (76.3%),
`Hex.ZPoly.reduceModPow` (46.6%) →
`Hex.List.mapTR.loop.at...reduceModPow.spec` (43.2%), and
`Hex.ZPoly.divModMonicModSquareAux` (35.1% / 22.2% stack entries)
for the divmod by the monic factor `g*` modulo `m²`.
`Hex.ZPoly.subModSquare` (16.1%) covers the `mod m²` differences,
and the Bezout-update `Hex.DensePoly.mul.at...bezoutCongrOn.spec`
(10.5%) covers the post-Bezout corrections `(s*g* + t*h*) - 1`.
The dominant work maps to the registered
`runQuadraticHenselStepChecksum` target via
`quadraticHenselStep → divModMonicModSquareAux → reduceModPow`,
matching the `n²` cost model for a single doubling step. The
single-step wallclock on this fixture is bounded regardless of the
seed Bezout pair, so the `(s, t) = (0, 1)` seed used here exercises
the same dense-arithmetic kernels as a full `xgcd`-derived seed
would.

Diagnostics:

```json
{
  "regions_total": 2,
  "total_timed_ms": 3459.363,
  "expected_samples_bench_thread": 3455.9,
  "retained_samples_bench_thread": 3451,
  "rejected_samples_bench_thread": 9,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142582089161000,
  "spawn_anchor_mono_ns": 330616009526541,
  "sidecar_mono_anchor_ns": 330616244060833,
  "samply_meta_start_time_ms": 1780142582098.1719
}
```

### `multifactor-lifting`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexhensel_bench \
    Hex.HenselBench.runMultifactorLiftQuadraticChecksum 192064 5000000000
```

Representative case: production quadratic ordered multifactor lift
of two prepared factors (`g` a fixed degree-1 monic factor, `h` a
deterministic dense degree-`193` integer polynomial,
`f = polyProduct [g, h] + 5*e`) lifted from `mod 5` to `mod 5^64` via
`⌈log₂ 64⌉ = 6` quadratic doublings, parameter
`encodeLiftParam 192 64 = 192_064`, no seed. Child row:
`inner_repeats=16`, `per_call_nanos=331393648.437500`,
`result_hash=0xe09bda79cfa1f787`. Leaf samples were own Hex code
55.6%, GMP 15.7%, Lean runtime 10.2%, allocation/free 5.7%, other
Lean/library code 4.3%, and other 8.4%. Inclusive own-code cost was
led by
`Hex.HenselBench.runMultifactorLiftQuadraticChecksum` (100.0%) →
`Hex.ZPoly.multifactorLiftQuadraticList` (99.8%) →
`Hex.ZPoly.henselLiftQuadratic` (99.8%) →
`Hex.ZPoly.iterateQuadraticHensel` (99.7%) →
`Hex.ZPoly.quadraticHenselStep`. Per-step work splits between the
Bezout-update `Hex.DensePoly.mul.at...bezoutCongrOn.spec` (36.5%),
`Hex.ZPoly.reduceModPow` (35.8%), and
`Hex.ZPoly.divModMonicModSquareAux` (20.6% / 18.1% stack entries)
for the divmod-by-`g*` step. The dominant work maps to the registered
`runMultifactorLiftQuadraticChecksum` target via
`multifactorLiftQuadraticList → henselLiftQuadratic →
iterateQuadraticHensel → quadraticHenselStep`, matching the
`n² · log₂ k` cost model for a binary lift through `⌈log₂ k⌉`
doublings. The two sibling registrations
`runMultifactorLiftChecksum` and `runPolyProductChecksum` share this
fixture and quadratic-corner code path; their scientific verdicts
both come back consistent at the same encoded `(n, k)` ladder, so a
single `multifactor-lifting` profile case suffices for the family.

Diagnostics:

```json
{
  "regions_total": 2,
  "total_timed_ms": 5632.061958,
  "expected_samples_bench_thread": 5626.4,
  "retained_samples_bench_thread": 5623,
  "rejected_samples_bench_thread": 11,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142589803135000,
  "spawn_anchor_mono_ns": 330623723584708,
  "sidecar_mono_anchor_ns": 330624011570833,
  "samply_meta_start_time_ms": 1780142589811.85
}
```

The dominant inclusive costs in all four profiles map to registered
`HexHensel/Bench.lean` targets. No unattributed dominant cost was
observed.

## Concerns

The post-comparator-pairing Hex / FLINT ratios surface two
algorithmic-shape findings that the headline report records rather
than gates on (the comparator is `informational`):

1. **Hex single-step lift carries a large constant factor against
   FLINT's tuned `lift_once`.** At the top of the LinearHenselStep
   ladder, Hex spends 83 ms per call at `n = 512` while FLINT returns
   the same single-step lift in 69 ms total (about 3 ms of
   algorithmic work after the 65.8 ms driver-spawn floor). The same
   pattern is sharper for `runQuadraticHenselStepChecksum`: Hex spends
   355 ms at `n = 512` while FLINT's algorithmic time stays under
   5 ms — about a 70× constant-factor gap. This reflects the
   schoolbook dense-arithmetic kernel Hex uses for the single Newton
   step against FLINT's word-level operand tuning; a future gating
   upgrade is owned by a separate SPEC PR per
   `SPEC/Libraries/hex-hensel.md §"External comparators"`, not
   delegated to an HO implementer.

2. **Python-emulated iterated lift is slower than Hex once
   `n ≥ 256`.** The driver implements the iterated lift via
   `fmpz_poly` arithmetic instead of the native C
   `nmod_poly_hensel_lift_*` entry points (python-flint does not
   bind them); the `fmpz_poly` operand sizes double per Newton step
   and the cost compounds super-linearly in `n`. At `n = 256, k = 8`
   the python emulation runs 3.2–3.8× slower than Hex across all
   three iterated-lift Hex surfaces. The comparator therefore shows
   FLINT *underperforming* Hex on the iterated lift only because of
   the python-emulation overhead, not because the algorithm is
   weaker; reading the iterated-lift ratios against the
   single-step ratios above isolates the emulation cost.
