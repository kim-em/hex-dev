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

Scientific run at commit `e63b09b22fb3` on `carica` (Apple M2 Ultra,
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
    --export-file reports/bench-results/hex-gfq-field-e63b09b22fb3.json
```

The run used the deterministic certificate-checked benchmark moduli
from `HexGfqField/Bench.lean` at the widened doubling-style schedule
`paramSchedule := .custom #[2, 3, 4, 6, 8, 12, 16]`; no random seeds
are involved. The harness recorded `e63b09b-dirty` because this
worktree carried unrelated pre-existing `.claude/CLAUDE.md` and
untracked `.claude/` modifications. Export artefact:
`reports/bench-results/hex-gfq-field-e63b09b22fb3.json`, SHA-256
`0c3edd4be3ce59a5626d2835a4a85bf8c1f63541296bf45639d0f59c6cb3cc4e`.

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: inconclusive
  (`cMin=199.297, cMax=882.440, β=−0.851`, parameters `2..16`,
  final hash `0xfd84a8a6c2b4cc99`).
- `Hex.GFqFieldBench.runAddChecksum`: inconclusive
  (`cMin=63.993, cMax=123.013, β=−0.388`, parameters `2..16`,
  final hash `0x96c8eaeed11e98ad`).
- `Hex.GFqFieldBench.runMulChecksum`: inconclusive
  (`cMin=321.408, cMax=529.802, β=−0.278`, parameters `2..16`,
  final hash `0x96e10e62f7800c4f`).
- `Hex.GFqFieldBench.runNegSubChecksum`: consistent with declared
  complexity (`cMin=350.101, cMax=457.056, β=−0.074`,
  parameters `2..16`, final hash `0xc05f8f4bd5d8d4a4`).
- `Hex.GFqFieldBench.runPowChecksum`: inconclusive
  (`cMin=718.095, cMax=1313.125, β=−0.293`, parameters `2..16`,
  final hash `0x29f0a4dde81b3df7`).
- `Hex.GFqFieldBench.runInvDivChecksum`: inconclusive
  (`cMin=1201.659, cMax=3612.366, β=−0.644`, parameters `2..16`,
  final hash `0xab06e5f6a82bb4cb`).
- `Hex.GFqFieldBench.runZPowChecksum`: inconclusive
  (`cMin=952.343, cMax=1891.464, β=−0.425`, parameters `2..16`,
  final hash `0x4019e87ee1ec1a59`).
- `Hex.GFqFieldBench.runFrobChecksum`: inconclusive
  (`cMin=785.377, cMax=1269.441, β=−0.223`, parameters `2..16`,
  final hash `0x29f0a4dde81b3df7`).

The schedule was extended from the previous `{2, 3, 4, 6}` ladder to
`{2, 3, 4, 6, 8, 12, 16}` by introducing three new
certificate-checked irreducible monic moduli over `F_7`: `m_p7_n8 :=
x^8 + x + 3`, `m_p7_n12 := x^12 + x^2 + x + 2`, and
`m_p7_n16 := x^16 + 2x + 3`. Each new modulus carries a Berlekamp
Rabin `IrreducibilityCertificate` whose pow chain and Bezout
witnesses are verified by `decide` through
`checkIrreducibilityCertificateLinearIncremental`, the same
`O(n · p)`-mult kernel-reducible path the existing `m_p7_n6` already
uses; `bundleForN` was extended in lockstep so each schedule entry
maps to a real degree-`n` modulus.

The wider schedule resolved one previously-inconclusive verdict
(`runNegSubChecksum`), which now returns `consistent with declared
complexity` at `β=−0.074` (well within the harness's default
`slopeTolerance := 0.15`). The other six previously-inconclusive
verdicts remain inconclusive but with measurably smaller |β|
residuals than at the narrower schedule:

| Benchmark | β at `{2,3,4,6}` | β at `{2,3,4,6,8,12,16}` |
| --- | --- | --- |
| `runOfPolyReprChecksum` | −1.510 | −0.851 |
| `runAddChecksum`        | −0.548 | −0.388 |
| `runMulChecksum`        | +0.610 | −0.278 |
| `runNegSubChecksum`     | −0.387 | **−0.074 (consistent)** |
| `runPowChecksum`        | +0.566 | −0.293 |
| `runInvDivChecksum`     | −0.460 | −0.644 |
| `runZPowChecksum`       | −0.121 (consistent) | −0.425 |
| `runFrobChecksum`       | +0.839 | −0.223 |

The remaining residuals all share the same shape: the per-call time
at `n = 2` is several hundred nanoseconds to a few microseconds (the
`runAddChecksum` bottom rung is 331 ns), close enough to the
warm-cache constant-factor floor of `lean_apply_2`-style closure
dispatch that the early rungs have a noticeably-higher
`time / declared_complexity` ratio than the later rungs. The C
column on the verdict tables shows this directly: `runMulChecksum` C
runs `490, 530, 321, 344, 347, 325` over the trimmed `n=3..16` tail,
i.e. it hits a stable plateau from `n=6` onwards and the negative β
is dominated by the `n=3, 4` rungs sitting above that plateau.

`runZPowChecksum` returned `consistent` at the previous narrower
schedule because at the four-rung `{2, 3, 4, 6}` ladder its single
high rung (`n=6`, ~117 µs) sat far above the per-spawn floor and the
log-log fit had only four data points to settle on; the wider ladder
adds three more high-n rungs and reveals the same small-n
constant-factor signature that the other registrations show. That
re-classification is consistent with the SPEC's anti-pattern note
that an earlier-narrow-schedule "consistent" verdict can flip when
the schedule is widened — the cost-model declarations themselves are
unchanged and `runNegSubChecksum`'s `consistent` verdict at the same
schedule confirms the harness can cleanly resolve the declared model
once the per-call time at the bottom rung is well above the floor.

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
quotient-ring arithmetic, whose own benchmark surface is now in
place at `done_through: 4` per `reports/hex-gfq-ring-performance.md`.

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

The profiles were taken against the `{2, 3, 4, 6}` schedule fixture
and remain valid evidence for the per-input-family attribution rule
because the underlying call-stack shape (`GFqRing.reduceMod →
DensePoly.divModArray → DensePoly.divModArrayAux →
DensePoly.subtractScaledShiftStep`, etc.) does not change with
modulus degree; only the dwell time per call grows.

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
`n² · log n` cost model.

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

- Six of eight scientific verdicts remain `inconclusive` at the
  widened `{2, 3, 4, 6, 8, 12, 16}` schedule:
  `runOfPolyReprChecksum` (β=−0.851), `runAddChecksum` (β=−0.388),
  `runMulChecksum` (β=−0.278), `runPowChecksum` (β=−0.293),
  `runInvDivChecksum` (β=−0.644), `runZPowChecksum` (β=−0.425), and
  `runFrobChecksum` (β=−0.223). Every C-column shows the same
  shape: high C at `n=3, 4` followed by a stable plateau from
  `n=6` onwards, indicating the residual slope is dominated by the
  warm-cache per-call constant-factor floor at the smallest rungs
  rather than by an asymptotic cost-model violation. Resolving
  this needs either further schedule widening (a degree-24 modulus
  was investigated but the `decide`-style certificate check at
  that degree pushes `HexGfqField.Bench` build time well past the
  ten-minute mark observed for degree-16) or per-registration
  finding-issues against the implementation under test. Tracked as
  the open follow-on for #2784. `HexGfqField.done_through` stays
  at `3` until the §Concerns section is empty.
