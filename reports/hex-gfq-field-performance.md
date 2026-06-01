# HexGFqField Performance Report

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
`libraries.yml`, wired in `HexGFqField/Bench.lean`, and covered by the
headline report; `HexGFqField.done_through` is therefore advanced to
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
`scripts/profile/run_profile.sh` at commit
`3bc24c50fbe57487776c433106894ee544a6d656-dirty` on `carica`
(Apple M2 Ultra, macOS 14.6.1, arm64) with `samply 0.13.1` at
999 Hz. The binary reported `lean_bench_version = 0.1.0` and
Lean `4.30.0-rc2`. The raw filtered Firefox Profiler JSON
artefacts are developer-local under `/tmp/hex-profile-*.json.gz`
and are not committed. Each profile keeps only samples from the
bench thread that fall inside LeanBench timed regions; input prep,
autotuner gaps, result hashing, and process exit samples are
excluded by the `lean-bench-samply` postprocessor. All percentages
below are leaf counts and inclusive counts as a fraction of those
filtered bench-thread samples.

### `dense-canonical-reduction`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfqfield_bench \
    Hex.GFqFieldBench.runOfPolyReprChecksum 8 1000000000
```

Representative case: deterministic dense `F_7`-coefficient
polynomial of size `2 * (n + 1) + 1` reduced through the
quotient-ring `ofPoly` constructor against the certificate-checked
modulus ladder, parameter `n = 8`, no seed. Leaf samples were own
Hex code 40.9%, Lean runtime 38.1%, GMP 9.9%, allocation/free
9.4%, other 1.7%. Inclusive own-code cost was led by the registered
`Hex.GFqFieldBench.runOfPolyReprChecksum` target (99.9%) and
`Hex.GFqRing.reduceMod` (99.7%); the reduction inner loop shows
`Hex.ZMod64.mul` (43.8%), division over coefficients
(`Hex.ZMod64.instDiv` / `Hex.ZMod64.inv`, 22.1% / 16.1%), and
`Hex.ZMod64.sub` (11.7%). The dominant work maps to the registered
`runOfPolyReprChecksum` target via the underlying `GFqRing.reduceMod`
quotient reduction, exactly as the `n²` cost model predicts.

Diagnostics:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='Thread <4456006>' tid=4456006
regions:            9, total timed = 747.1 ms
expected samples:   ~746 on bench thread
retained samples:   746 on bench thread (11 rejected outside windows)
other-thread noise: 0 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runOfPolyReprChecksum-8.json.gz
calibration anchors: spawn_wall_ns=1780141959048101000, spawn_mono_ns=329992961637291,
    sidecar_mono_anchor_ns=329993403086583, samply_start_time_ms=1780141959068.94
```

### `field-arithmetic`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfqfield_bench \
    Hex.GFqFieldBench.runMulChecksum 8 1000000000
```

Representative case: deterministic dense `F_7` canonical-rep
polynomial pairs of size `n + 1` multiplied modulo the
certificate-checked modulus ladder, parameter `n = 8`, no seed.
Leaf samples were own Hex code 45.5%, Lean runtime 36.0%, allocation
/ free 9.2%, GMP 7.9%, other 1.3%. Inclusive own-code cost was led
by `Hex.GFqFieldBench.runMulChecksum` (99.7%),
`Hex.ZMod64.mul` (54.9%), `Hex.GFqRing.reduceMod` (52.2%),
`Hex.GFqRing.mul` (47.4%), and `Hex.DensePoly.mul` (46.6%).
Reduction-side coefficient division remains visible through
`Hex.ZMod64.instDiv` / `Hex.ZMod64.inv` (10.4% / 8.5%), but the
main shape is the multiplication target plus its post-multiply
quotient reduction. The dominant work maps to the registered
`runMulChecksum` target via
`GFqRing.mul` and the `GFqRing.reduceMod` post-multiplication
reduction, matching the `n²` cost model.

Diagnostics:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='Thread <4465323>' tid=4465323
regions:            9, total timed = 749.4 ms
expected samples:   ~749 on bench thread
retained samples:   749 on bench thread (7 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runMulChecksum-8.json.gz
calibration anchors: spawn_wall_ns=1780141965622885000, spawn_mono_ns=329999536493291,
    sidecar_mono_anchor_ns=329999763305458, samply_start_time_ms=1780141965630.483
```

### `field-exponentiation`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfqfield_bench \
    Hex.GFqFieldBench.runZPowChecksum 8 1000000000
```

Representative case: signed square-and-multiply of canonical-rep
field elements with negative dense exponents at the
certificate-checked modulus ladder, parameter `n = 8`, no seed.
Leaf samples were own Hex code 43.3%, Lean runtime 37.4%, allocation
/ free 8.7%, GMP 8.7%, other 2.0%. Inclusive own-code cost was led
by `Hex.GFqFieldBench.runZPowChecksum` (100.0%),
`Hex.GFqField.zpow` (71.9%) and `Hex.GFqRing.pow.go` (71.7%) for the
signed square-and-multiply chain. The negative-exponent tail remains
visible as `Hex.GFqField.inv` (28.0%), `Hex.GFqField.invPoly`
(27.5%), and `Hex.DensePoly.xgcd` (27.3%). Multiplications inside
the exponentiation account for `Hex.ZMod64.mul` (46.4%),
`Hex.DensePoly.mul` (42.7%), `Hex.GFqRing.reduceMod` (38.2%), and
`Hex.GFqRing.mul` (33.5%). The dominant work maps to the registered
`runZPowChecksum` target via
`GFqField.zpow → GFqRing.pow.go + GFqField.inv`, matching the
`n² · log n` cost model.

Diagnostics:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='Thread <4475688>' tid=4475688
regions:            5, total timed = 1007.4 ms
expected samples:   ~1006 on bench thread
retained samples:   1005 on bench thread (10 rejected outside windows)
other-thread noise: 0 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runZPowChecksum-8.json.gz
calibration anchors: spawn_wall_ns=1780141972881916000, spawn_mono_ns=330006795603791,
    sidecar_mono_anchor_ns=330007096922083, samply_start_time_ms=1780141972889.7358
```

### `field-inversion-division`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexgfqfield_bench \
    Hex.GFqFieldBench.runInvDivChecksum 8 1000000000
```

Representative case: canonical-rep field inversion combined with
canonical-rep field division at the certificate-checked modulus
ladder, parameter `n = 8`, no seed. Leaf samples were own Hex code
40.9%, Lean runtime 35.7%, allocation/free 11.1%, GMP 9.2%, other
3.0%. Inclusive own-code cost was led by
`Hex.GFqFieldBench.runInvDivChecksum` (100.0%),
`Hex.GFqField.inv` (84.7%), `Hex.GFqField.invPoly` (82.4%), and
`Hex.DensePoly.xgcd` (81.4%); `Hex.GFqField.div` (46.1%) accounts
for the division half through one further inverse plus
`GFqRing.mul`. Subordinate dense arithmetic appears as
`Hex.ZMod64.mul` (36.6%), `Hex.DensePoly.mul` (33.1%),
`Hex.ZMod64.sub` (22.0%), `Hex.ZMod64.complementWord` (18.8%), and
`Hex.DensePoly.sub` (15.1%) inside the Euclidean chain. The dominant
work maps to the registered `runInvDivChecksum` target via
`GFqField.inv` and `GFqField.div`, matching the `n²` cost model.

Diagnostics:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='Thread <4484641>' tid=4484641
regions:            6, total timed = 597.0 ms
expected samples:   ~596 on bench thread
retained samples:   596 on bench thread (10 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runInvDivChecksum-8.json.gz
calibration anchors: spawn_wall_ns=1780141979062884000, spawn_mono_ns=330012976639833,
    sidecar_mono_anchor_ns=330013199594916, samply_start_time_ms=1780141979069.74
```

## Concerns

None.
