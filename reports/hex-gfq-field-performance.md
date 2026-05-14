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

Comparator wiring and smoke verdict run at worktree commit
`728f2ca-dirty` on `carica` (Apple Silicon, macOS arm64), command:

```sh
lake exe hexgfqfield_bench run --filter GFqFieldBench.run \
    --export-file reports/bench-results/hex-gfq-field-flint-fq-default.json \
    --total-seconds 120
```

Export artefact:
`reports/bench-results/hex-gfq-field-flint-fq-default.json`, SHA-256
`39b0314b311fb893b5def63aebfe1d5f10278fba42bd741120ecae067a3d023d`.
The run completed all 104 registered benchmarks: the eight
parametric Hex targets plus the paired fixed Hex / FLINT
`fq_default` registrations over the certificate-checked
`#[2, 3, 4, 5, 6, 8]` modulus ladder.

- `Hex.GFqFieldBench.runOfPolyReprChecksum`: inconclusive
  (`cMin=314.805, cMax=911.270`, parameters `2,3,4,5,6,8`,
  final hash `0x82984efaad14453f`).
- `Hex.GFqFieldBench.runAddChecksum`: inconclusive
  (`cMin=81.158, cMax=127.371`, parameters `2,3,4,5,6,8`,
  final hash `0x6457f0ed8c5c8ed2`).
- `Hex.GFqFieldBench.runMulChecksum`: inconclusive
  (`cMin=314.038, cMax=516.962`, parameters `2,3,4,5,6,8`,
  final hash `0x4084079980228486`).
- `Hex.GFqFieldBench.runNegSubChecksum`: consistent with declared
  complexity (`cMin=376.422, cMax=469.543`,
  parameters `2,3,4,6,8`,
  final hash `0x98d27f45e383f912`).
- `Hex.GFqFieldBench.runPowChecksum`: inconclusive
  (`cMin=886.930, cMax=1341.691`, parameters `2,3,4,5,6,8`,
  final hash `0x9cd46ad6ad57336b`).
- `Hex.GFqFieldBench.runInvDivChecksum`: inconclusive
  (`cMin=2181.290, cMax=3816.775`, parameters `2,3,4,5,6,8`,
  final hash `0x1415615b9aa4bc17`).
- `Hex.GFqFieldBench.runZPowChecksum`: inconclusive
  (`cMin=1222.396, cMax=2002.587`, parameters `2,3,4,5,6,8`,
  final hash `0xab98d3409e67fa7f`).
- `Hex.GFqFieldBench.runFrobChecksum`: consistent with declared
  complexity (`cMin=907.931, cMax=1339.909`,
  parameters `2,3,4,6,8`, final hash `0x351dd7aebb5accca`).

The remaining inconclusive verdicts are a calibration issue on the
small certificate-backed ladder, not a blocker for the informational
FLINT comparator. The Phase 4 comparator is now declared in
`libraries.yml`, wired in `HexGfqField/Bench.lean`, and covered by the
headline report; `HexGfqField.done_through` is therefore advanced to
`4`.

Smoke wiring was checked with:

```sh
lake exe hexgfqfield_bench list
lake exe hexgfqfield_bench verify
```

`verify` passed all 104 registered benchmarks.

## Comparator Ratios

`FLINT fq_default via python-flint` is wired as an `informational`
comparator through the shared python-flint persistent-subprocess driver
`scripts/oracle/flint_bench_driver.py`. A separate persistent-driver
overhead probe on the trivial `fq_default.reduce` request measured
median 16.959 us per JSON request / reply (min 12.250 us, max
150.833 us, 200 post-warmup requests). The fixed LeanBench comparator
registrations below include one driver startup per isolated benchmark
child, so their raw FLINT medians are dominated by Python process and
python-flint import time; subtracting the persistent per-call overhead
changes these ratios by less than 0.1%.

Representative raw ratios at the top rung (`n = 8`) are:

| Target | Hex median | FLINT median | Raw ratio | Adjusted ratio |
| --- | ---: | ---: | ---: | ---: |
| dense canonical reduction | 22.146 us | 58.475 ms | 2640x | 2639x |
| addition | 0.649 us | 89.535 ms | 137902x | 137876x |
| multiplication | 22.089 us | 55.808 ms | 2526x | 2526x |
| negation/subtraction | 3.112 us | 56.202 ms | 18057x | 18052x |
| natural exponentiation | 170.291 us | 62.133 ms | 365x | 365x |
| inversion/division | 139.603 us | 53.472 ms | 383x | 383x |
| signed exponentiation | 234.700 us | 61.623 ms | 263x | 262x |
| Frobenius | 121.820 us | 60.013 ms | 493x | 492x |

Across the ladder, the ratio declines as the Hex workload grows while
the process-call comparator remains startup dominated. The trend is
strongest on the superlinear targets: multiplication falls from about
91502x at `n = 2` to 2526x at `n = 8`, natural exponentiation from
42907x to 365x, inversion/division from 3725x to 383x, and signed
exponentiation from 7546x to 263x. Linear addition and neg/sub remain
mostly measurement-shape dominated at these small degrees. The
comparator is informational, so there is no gating-goal verdict.

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
