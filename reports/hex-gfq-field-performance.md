# HexGfqField Performance Report

## Bench Targets

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: `n * n`
- `Hex.GFqFieldBench.runAddChecksum`: `n`
- `Hex.GFqFieldBench.runMulChecksum`: `n * n`
- `Hex.GFqFieldBench.runNegSubChecksum`: `n`
- `Hex.GFqFieldBench.runPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqFieldBench.runInvDivChecksum`: `n * n`
- `Hex.GFqFieldBench.runZPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqFieldBench.runFrobChecksum`: `n * n * Nat.log2 7`

## Verdicts

Scientific follow-up run at worktree commit `713a73d5754` on `carica`
(Apple Silicon, macOS arm64), command:

```sh
lake exe hexgfqfield_bench run \
    Hex.GFqFieldBench.runOfPolyReprChecksum \
    Hex.GFqFieldBench.runAddChecksum \
    Hex.GFqFieldBench.runMulChecksum \
    Hex.GFqFieldBench.runNegSubChecksum \
    Hex.GFqFieldBench.runPowChecksum \
    Hex.GFqFieldBench.runInvDivChecksum \
    Hex.GFqFieldBench.runZPowChecksum \
    Hex.GFqFieldBench.runFrobChecksum \
    --export-file reports/bench-results/hex-gfq-field-n5-n8-schedule.json
```

The run used the deterministic benchmark moduli from
`HexGfqField/Bench.lean` at
`paramSchedule := .custom #[2, 3, 4, 5, 6, 8]` for the six
previously inconclusive targets and the existing
`#[2, 3, 4, 6, 8]` schedule for the already-consistent neg/sub and
Frobenius targets; no random seeds are involved. The degree-5 rung
is the small certificate-checked irreducible monic modulus
`m_p7_n5 := x^5 + x + 4`, adding a mid-ladder calibration point
without pulling in a Conway dependency or degree-12/16 certificate
elaboration. The harness recorded `713a73d-dirty` because this run
was made from the active worktree containing the schedule edit.
Export artefact:
`reports/bench-results/hex-gfq-field-n5-n8-schedule.json`, SHA-256
`e2fc068af1ddf6a781ddbe7a75f9f43ad6ca2db3dcd7e499d017d0aa7c7d815c`.

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: inconclusive
  (`cMin=313.133, cMax=918.817`, parameters `2,3,4,5,6,8`,
  final hash `0x82984efaad14453f`).
- `Hex.GFqFieldBench.runAddChecksum`: inconclusive
  (`cMin=81.544, cMax=128.528`, parameters `2,3,4,5,6,8`,
  final hash `0x6457f0ed8c5c8ed2`).
- `Hex.GFqFieldBench.runMulChecksum`: inconclusive
  (`cMin=309.870, cMax=525.271`, parameters `2,3,4,5,6,8`,
  final hash `0x4084079980228486`).
- `Hex.GFqFieldBench.runNegSubChecksum`: consistent with declared
  complexity (`cMin=384.250, cMax=470.554`,
  parameters `2,3,4,6,8`,
  final hash `0x98d27f45e383f912`).
- `Hex.GFqFieldBench.runPowChecksum`: inconclusive
  (`cMin=864.125, cMax=1318.216`, parameters `2,3,4,5,6,8`,
  final hash `0x9cd46ad6ad57336b`).
- `Hex.GFqFieldBench.runInvDivChecksum`: inconclusive
  (`cMin=2159.953, cMax=3740.486`, parameters `2,3,4,5,6,8`,
  final hash `0x1415615b9aa4bc17`).
- `Hex.GFqFieldBench.runZPowChecksum`: inconclusive
  (`cMin=1194.725, cMax=1956.204`, parameters `2,3,4,5,6,8`,
  final hash `0xab98d3409e67fa7f`).
- `Hex.GFqFieldBench.runFrobChecksum`: consistent with declared
  complexity (`cMin=921.583, cMax=1348.282`,
  parameters `2,3,4,6,8`, final hash `0x351dd7aebb5accca`).

The degree-5 rung adds a CI-safe calibration point between the
existing degree-4 and degree-6 fixtures. This widens the scientific
evidence without changing executable semantics or adding degree-12/16
certificate elaboration to the normal benchmark module.

The remaining six inconclusive verdicts keep `HexGfqField` below
Phase 4 completion. The dominant shape remains calibration rather
than a model change: several targets still have bottom rungs close to
the sub-microsecond or low-microsecond warm-cache floor, and the
degree-5 point does not materially change the verdict reduction. The
cost-model declarations therefore remain unchanged,
`libraries.yml: HexGfqField.done_through` remains `3`, and the open
concern is still a larger calibration path that widens the evidence
without adding CI-heavy degree-12/16 certificate elaboration to the
normal benchmark module.

Smoke wiring was also checked at the same commit with:

```sh
lake exe hexgfqfield_bench list
lake exe hexgfqfield_bench verify
```

`verify` passed all eight registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-gfq-field.md` does not name an external Phase-4
performance comparator for `HexGfqField`, so there are no
`phase4.comparators` ratios to record. The library is layered on
`HexGfqRing` and the field-level cost is dominated by the underlying
quotient-ring arithmetic, which carries its own (also-pending)
benchmark surface (#2734).

## Profile

Profiles were recorded with
`samply record --save-only --unstable-presymbolicate` at commit
`523de1997cfb` on `carica` (Apple M2 Ultra, macOS 14.6.1) at the
default 1 kHz sampling rate. The raw Firefox Profiler JSON
artefacts and their `.syms.json` symbol sidecars are
developer-local and are not committed. Each profile sums samples
from the `hexgfqfield_bench` worker child processes only, not the
orchestrator (whose wallclock is dominated by `__read_nocancel`
waits for the child stdout that LeanBench's subprocess-isolated
harness produces). All percentages below are leaf counts and
inclusive counts as a fraction of those child-only samples.

### `dense-canonical-reduction`

Command:

```sh
samply record --save-only --unstable-presymbolicate \
    -o reports/bench-results/profiles/hex-gfq-field-of-poly-repr-523de1997cfb.json \
    -- lake exe hexgfqfield_bench run Hex.GFqFieldBench.runOfPolyReprChecksum
```

Representative case: deterministic dense `F_7`-coefficient
polynomial of size `2 * (n + 1) + 1` reduced through the
quotient-ring `ofPoly` constructor against the certificate-checked
modulus ladder, parameters `2..6`, no seed. Leaf samples were Lean
runtime 31.3%, allocation/free 28.5%, kernel/syscall wait 11.7%,
GMP 8.7%, own HexGfqField/HexGfqRing/HexPolyFp code 6.6%, other
13.1%. Inclusive own-code cost was led by
`Hex.GFqRing.reduceMod` (74.5%) → `Hex.DensePoly.divModArray`
(73.6%) → `Hex.DensePoly.divModArrayAux` (70.5%) →
`Hex.DensePoly.subtractScaledShiftStep` (42.8%); per-coefficient
work appears as `Hex.ZMod64.mul` (22.8%), `Hex.ZMod64.sub` (15.5%),
`Hex.ZMod64.inv` (14.6%), and `Hex.ZMod64.complementWord` (13.5%).
The dominant work maps to the registered
`runOfPolyReprChecksum` target via the underlying `GFqRing.reduceMod`
quotient reduction, exactly as the `n²` cost model predicts.

### `field-arithmetic`

Command:

```sh
samply record --save-only --unstable-presymbolicate \
    -o reports/bench-results/profiles/hex-gfq-field-mul-523de1997cfb.json \
    -- lake exe hexgfqfield_bench run Hex.GFqFieldBench.runMulChecksum
```

Representative case: deterministic dense `F_7` canonical-rep
polynomial pairs of size `n + 1` multiplied modulo the
certificate-checked modulus ladder, parameters `2..6`, no seed.
Leaf samples were Lean runtime 30.5%, allocation/free 29.5%,
kernel/syscall wait 12.8%, own code 7.5%, GMP 5.6%, other 14.2%.
Inclusive own-code cost was led by `Hex.GFqRing.reduceMod` (36.7%)
and `Hex.GFqRing.mul` (34.7%), with
`Hex.DensePoly.divModArray` (33.3%) and `Hex.DensePoly.mul` (30.6%)
sharing the heavy lifting; per-coefficient work appears as
`Hex.ZMod64.mul` (29.7%) and `Hex.ZMod64.inv` (6.7%) (the latter
through `ZMod64.instDiv.hexPolyFp.redArg.lam`, used inside the
`subtractScaledShiftStep` reduction inner loop). The dominant work
maps to the registered `runMulChecksum` target via
`GFqRing.mul` and the `GFqRing.reduceMod` post-multiplication
reduction, matching the `n²` cost model.

### `field-exponentiation`

Command:

```sh
samply record --save-only --unstable-presymbolicate \
    -o reports/bench-results/profiles/hex-gfq-field-zpow-523de1997cfb.json \
    -- lake exe hexgfqfield_bench run Hex.GFqFieldBench.runZPowChecksum
```

Representative case: signed square-and-multiply of canonical-rep
field elements with negative dense exponents at the
certificate-checked modulus ladder, parameters `2..6`, no seed. Leaf
samples were Lean runtime 33.3%, allocation/free 26.0%,
kernel/syscall wait 14.2%, own code 6.4%, GMP 6.1%, other 14.0%.
Inclusive own-code cost was led by `Hex.GFqField.zpow` (36.3%) which
splits into `Hex.GFqRing.pow.go` (36.2%) for the natural
square-and-multiply chain and `Hex.GFqField.inv` (31.3%) for the
final negative-exponent inversion;
`Hex.DensePoly.divModArray` (35.1%) and `Hex.DensePoly.xgcd` (29.4%)
appear in roughly equal share, reflecting that each multiplication
inside `pow.go` reduces modulo the modulus and the trailing
inversion runs one extended-gcd against it. The dominant work maps
to the registered `runZPowChecksum` target via
`GFqField.zpow → GFqRing.pow.go + GFqField.inv`, matching the
`n² · log n` cost model. This is the only verdict-consistent
registration in this snapshot, and its profile attributes the cost
exactly where the model expects.

### `field-inversion-division`

Command:

```sh
samply record --save-only --unstable-presymbolicate \
    -o reports/bench-results/profiles/hex-gfq-field-inv-div-523de1997cfb.json \
    -- lake exe hexgfqfield_bench run Hex.GFqFieldBench.runInvDivChecksum
```

Representative case: canonical-rep field inversion combined with
canonical-rep field division at the certificate-checked modulus
ladder, parameters `2..6`, no seed. Leaf samples were Lean runtime
32.7%, allocation/free 27.4%, kernel/syscall wait 13.6%, own code
6.9%, GMP 6.8%, other 12.6%. Inclusive own-code cost was led by
`Hex.GFqField.inv` (59.4%) → `Hex.GFqField.invPoly` (57.3%) →
`Hex.DensePoly.xgcd` (55.5%) → `Hex.DensePoly.xgcdAux` (55.4%);
`Hex.GFqField.div` (32.0%) accounts for the division half of the
benchmark via one further `GFqField.inv` plus `GFqRing.mul`.
Subordinate `Hex.DensePoly.mul` (17.2%), `Hex.DensePoly.sub`
(13.5%), and `Hex.DensePoly.subtractScaledShiftStep` (12.4%) inside
`xgcdAux` round out the dense-coefficient surface. The dominant
work maps to the registered `runInvDivChecksum` target via
`GFqField.inv` (which exercises the `DensePoly.xgcd` Euclidean
remainder chain over `F_7`), matching the `n²` cost model.

## Concerns

- #2801: The CI-feasible degree-8 ladder resolves
  `runNegSubChecksum` and `runFrobChecksum`, and the CI-safe
  degree-5 certificate widens the six unresolved calibration
  schedules to `2,3,4,5,6,8`, but those six scientific verdicts
  remain inconclusive
  (`runOfPolyReprChecksum`, `runAddChecksum`, `runMulChecksum`,
  `runPowChecksum`, `runInvDivChecksum`, `runZPowChecksum`).
  `HexGfqField.done_through` stays at `3` until a larger calibration
  path widens the evidence without putting degree-12/16 certificate
  checks on the normal CI build path.
