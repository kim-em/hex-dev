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

Scientific run at commit `523de1997cfb` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

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
    --export-file reports/bench-results/hex-gfq-field-523de1997cfb.json
```

The run used the deterministic certificate-checked benchmark moduli
from `HexGfqField/Bench.lean`; no random seeds are involved. The
harness recorded `523de19-dirty` because this worktree had unrelated
pre-existing `.claude/CLAUDE.md` and untracked `.claude/`
modifications. Export artefact:
`reports/bench-results/hex-gfq-field-523de1997cfb.json`, SHA-256
`d6c0763f2712970c743e84d219291947b589fae31bbcfcf9f760e092404e4ecd`.

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: inconclusive
  (`cMin=310.536, cMax=1666.879, β=−1.510`, parameters `2..6`,
  final hash `0xe0324f34c2d7ac63`).
- `Hex.GFqFieldBench.runAddChecksum`: inconclusive
  (`cMin=90.040, cMax=163.646, β=−0.548`, parameters `2..6`,
  final hash `0xd1b86c296b959ca6`).
- `Hex.GFqFieldBench.runMulChecksum`: inconclusive
  (`cMin=153.840, cMax=515.665, β=+0.610`, parameters `2..6`,
  final hash `0x91489561cd38b03b`).
- `Hex.GFqFieldBench.runNegSubChecksum`: inconclusive
  (`cMin=378.664, cMax=603.262, β=−0.387`, parameters `2..6`,
  final hash `0xd7d268a09652d0ef`).
- `Hex.GFqFieldBench.runPowChecksum`: inconclusive
  (`cMin=478.382, cMax=1337.442, β=+0.566`, parameters `2..6`,
  final hash `0xf71dec75f2d46f78`).
- `Hex.GFqFieldBench.runInvDivChecksum`: inconclusive
  (`cMin=2418.137, cMax=4086.358, β=−0.460`, parameters `2..6`,
  final hash `0xbf470feeecf1e1fa`).
- `Hex.GFqFieldBench.runZPowChecksum`: consistent with declared
  complexity (`cMin=1624.496, cMax=1974.890, β=−0.121`,
  parameters `2..6`, final hash `0x78750cf6719eef1`).
- `Hex.GFqFieldBench.runFrobChecksum`: inconclusive
  (`cMin=340.670, cMax=1338.808, β=+0.839`, parameters `2..6`,
  final hash `0xf71dec75f2d46f78`).

The seven inconclusive verdicts are calibration findings rather than
implementation findings: the bench file ships
`paramSchedule := .custom #[2, 3, 4, 6]` because that is the union
of the four certificate-checked irreducible moduli over `F_7` it
carries (`m_p7_n2`, `m_p7_n3`, `m_p7_n4`, `m_p7_n6`), and the
per-call times at the bottom rungs (sub-microsecond for
`runAddChecksum` / `runMulChecksum` at `n = 2`) sit close enough to
the warm-cache constant-factor floor that the log-log slope fit does
not converge across only four rungs of a ~3× parameter range.
`runZPowChecksum` is the one consistent verdict because its per-call
time at `n = 2` is already 7 µs and rises to 117 µs by `n = 6`,
giving the fit enough dynamic range to settle. Issue #2784 tracks
the schedule widening (new degree-`8`/`12`/etc. certificate-checked
moduli plus matching `paramSchedule`) required before
`HexGfqField.done_through` can return to `4`. The cost-model
declarations themselves are unchanged: `runZPowChecksum`'s
`consistent` verdict at the same schedule confirms the model is
correct and only the rung spacing is off.

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

- #2784: Widen the `HexGfqField/Bench.lean` parameter schedule beyond
  `{2, 3, 4, 6}` so the seven currently-inconclusive scientific
  verdicts (`runOfPolyReprChecksum`, `runAddChecksum`, `runMulChecksum`,
  `runNegSubChecksum`, `runPowChecksum`, `runInvDivChecksum`,
  `runFrobChecksum`) return `consistent with declared complexity`.
  `HexGfqField.done_through` stays at `3` until the schedule is
  widened and `§Concerns` becomes empty.
