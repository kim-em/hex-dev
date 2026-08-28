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

All eight parametric performance registrations use **mode 1, two-sided
parametric**. Their adjacent derivations determine the expected family scaling
before measurement:
coefficientwise addition is linear, dense multiplication/reduction and
extended gcd are quadratic, and exponentiation repeats quadratic
multiplication logarithmically. The scientific schedule is
`#[2, 432, 600, 768, 936, 1216]`: degree 2 retains a smoke point, while the
five-point verdict tail spans more than a factor of `e`. Every tail degree is
`40 mod 56`, so the deterministic dense operands have the same coefficient
pattern over `F_7`; only their degree changes.

The high-degree sparse trinomials are checked by `Berlekamp.rabinTest` during
compiled benchmark preparation, and the proven implication from that check
supplies each field's irreducibility witness. Ordinary elaboration still
contains only the static degree-2-through-8 certificates. Thus `verify`, which
uses parameters 0 and 1, does not generate or elaborate the scientific
fixtures. The scientific registrations use three outer trials, warm-cache
medians, a 120-second per-call cap, and the same schedule for all eight models.

The 96 fixed registrations are comparator endpoints and canonical
expected-hash checks. They make no complexity claim, have no mode, and do not
replace the eight performance registrations.

The clean scientific run at commit
`97ff768e53567c607c2afb8942295314c35ed3b9` on `chungus2` (AMD EPYC 9455,
Linux x86-64, Lean 4.34.0-rc2) used two direct harness invocations:

```sh
lake exe hexgfqfield_bench run \
  Hex.GFqFieldBench.runOfPolyReprChecksum \
  Hex.GFqFieldBench.runNegSubChecksum \
  Hex.GFqFieldBench.runPowChecksum \
  Hex.GFqFieldBench.runInvDivChecksum \
  Hex.GFqFieldBench.runFrobChecksum \
  --export-file reports/bench-results/hex-gfq-field-scientific-core-9740.json

lake exe hexgfqfield_bench run \
  Hex.GFqFieldBench.runAddChecksum \
  Hex.GFqFieldBench.runMulChecksum \
  Hex.GFqFieldBench.runZPowChecksum \
  --export-file reports/bench-results/hex-gfq-field-scientific-holdouts-9740.json
```

The artefacts are unmodified exports from those commands. Their SHA-256 sums
are respectively
`2335f01b8c0d3b77adf858ce42eb836d56df2a1764ec75caef649bd93d34807f`
and
`9d047aa1c878e44e117a8a325fe945378545a8201d164423f165ed8db11f62bb`.
Both top-level and per-result environments record the full commit above and
`git_dirty=false`. Splitting the registrations limits sustained host drift;
each verdict is produced directly by the harness, with no row combination or
post-processing.

| Registration | Model | `cMin` | `cMax` | slope | degree-1216 hash |
|---|---:|---:|---:|---:|---:|
| `runOfPolyReprChecksum` | `n * n` | 14.969 | 17.601 | +0.117 | `0x7d4ede102dccc098` |
| `runAddChecksum` | `n` | 15.201 | 16.378 | +0.053 | `0x7104d75758a05e8b` |
| `runMulChecksum` | `n * n` | 18.534 | 20.124 | +0.015 | `0xce29294f4da9426b` |
| `runNegSubChecksum` | `n` | 65.493 | 69.065 | +0.047 | `0xe4ecaaefaae0627e` |
| `runPowChecksum` | `n * n * Nat.log2 (n + 1)` | 40.441 | 41.488 | -0.026 | `0x330820cab12539dd` |
| `runInvDivChecksum` | `n * n` | 48.905 | 69.209 | -0.037 | `0x7845bac0524b037c` |
| `runZPowChecksum` | `n * n * Nat.log2 (n + 1)` | 49.974 | 52.785 | -0.054 | `0x4619a8eb8cf05b54` |
| `runFrobChecksum` | `n * n * Nat.log2 7` | 46.266 | 47.960 | -0.003 | `0x736ff013e830511` |

Every registration is **consistent with declared complexity** under the
mode-1 two-sided rule, so the Phase-4 gate passes. The informational FLINT
comparator remains declared in `libraries.yml`, wired in
`HexGFqField/Bench.lean`, and covered by this report's comparator section.

Smoke wiring was checked with:

```sh
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

Six mode-1 registrations remain inconclusive on the narrow
certificate-backed ladder. The pre-policy report already identified this as
miscalibration, and the ordered rule does not change it into a pass. No clean
scientific run exists for any of the eight registrations.
This finding and the rollback are recorded by
[#9733](https://github.com/kim-em/hex-dev/issues/9733); a focused remediation
issue follows after the policy lands.
