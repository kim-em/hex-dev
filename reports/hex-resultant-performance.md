# HexResultant Performance Report

## Bench Targets

The four parametric registrations in `bench/HexResultant/Bench.lean` use these
declared complexity expressions, copied from their registration sites:

- `Hex.ResultantBench.runPseudoDiv`: `n * n * n`
- `Hex.ResultantBench.runChain`: `wallCostModel n`
- `Hex.ResultantBench.runResultant`: `wallCostModel n`
- `Hex.ResultantBench.runDisc`: `wallCostModel n`

Here `wallCostModel n` is defined adjacent to the registrations as
`n * n * (Nat.log2 (n + 1) + 1)`. The shared seed-`0xC0FFEE`
`bounded-dense-polynomial-prs` family uses equal-degree pairs at
`#[4, 6, 8, 10, 12, 16, 20, 24, 32]` for Brown chains, resultants, and
discriminants. Pseudo-division uses a degree-`n` dividend and degree-`n / 2`
divisor at `#[24, 32, 40, 48, 64, 80, 96, 128]`.

The resultant and discriminant ladders also have one fixed Hex registration and
one fixed FLINT registration per rung. `runFlintOverhead` is an auxiliary fixed
registration for persistent-driver protocol calibration; it has no polynomial
work and makes no algorithmic-complexity claim.

## Verdicts

The scientific run used LeanBench 0.1.0 and Lean 4.33.0-rc1 on clean commit
`4dee6f04bc121df8ac3ff09ba31554b7d0954a18`, host `chungus2` (Linux x86-64,
AMD EPYC 9455 48-Core Processor), with three outer trials per rung:

```sh
lake exe hexresultant_bench run \
  Hex.ResultantBench.runPseudoDiv Hex.ResultantBench.runChain \
  Hex.ResultantBench.runResultant Hex.ResultantBench.runDisc \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-resultant-4dee6f04-scientific.json
```

The export is
`reports/bench-results/hex-resultant-4dee6f04-scientific.json`, SHA-256
`c7489a8cf954b93eccb78e631af0ee6467089ae0aaa6924e4be8e1e9bff7ae9c`.
Every rung was above the configured signal floor and participated in its
verdict.

- `runPseudoDiv`: consistent with declared complexity (`beta=-0.249`,
  `cMin=0.281`, `cMax=0.641`).
- `runChain`: consistent with declared complexity (`beta=+0.116`,
  `cMin=43.913`, `cMax=57.034`).
- `runResultant`: consistent with declared complexity (`beta=-0.027`,
  `cMin=40.925`, `cMax=53.740`).
- `runDisc`: consistent with declared complexity (`beta=-0.007`,
  `cMin=41.232`, `cMax=53.529`).

The fixed runs used five measured repeats with at least 0.2 s of auto-tuned
inner repetitions per child. The tables in Comparator Ratios enumerate the
median of every fixed registration. The Hex and FLINT observed hashes agree at
every one of the 18 paired rungs. Smoke verification after adding the overhead
probe also passed all 41 registrations:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench verify
```

## Comparator Ratios

The SPEC and `libraries.yml` classify
`FLINT fmpz_poly resultant/discriminant via python-flint` as informational.
The implementation uses python-flint 0.9.0 and the shared persistent JSON-line
driver; FLINT/PARI correctness remains independently checked by the Resultant
conformance oracle.

Steady-state protocol overhead was measured with the no-work
`fmpz_poly.overhead` request at clean commit
`af9c82b25e401544280b71525f71ec688d980b03` on the same host:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run Hex.ResultantBench.runFlintOverhead \
  --repeats 11 --min-total-seconds 0.5 \
  --export-file reports/bench-results/hex-resultant-af9c82b2-flint-overhead.json
```

The median was **6.020 us** per request/reply (minimum 5.867 us, maximum
6.845 us), with 131072 warm requests in each outer repeat. The export is
`reports/bench-results/hex-resultant-af9c82b2-flint-overhead.json`, SHA-256
`84f64219e11c9f0a5ac845d3a06081de9649812fef09b7ab1265d9effcecf3e4`.
Every comparator median below has more than 5% protocol overhead, so each table
shows both `raw = FLINT / Hex` and
`adjusted = (FLINT - 6.020 us) / Hex`. Eligibility means that overhead is at
most 50% of the FLINT median and the call is below the 10 s ceiling.

### Resultant

The clean fixed-resultant run at commit
`39159455770ddf6e17f6580e63657b4bd10ee78f` used:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run \
  $(lake exe hexresultant_bench list | \
    awk '$1 ~ /run(Flint)?Resultant[0-9]+$/ {print $1}') \
  --export-file reports/bench-results/hex-resultant-39159455-flint-resultant.json
```

The export SHA-256 is
`ddc6616554e61c55b1dd6fdbe6a0765c4ba07d0d625351faf8def04f6774154d`.

| n | Hex median | FLINT median | observed hash (both) | raw | adjusted | eligible |
|---:|---:|---:|---:|---:|---:|:---:|
| 4 | 2.557 us | 10.024 us | `0x4333fb` | 3.920x | 1.566x | no |
| 6 | 6.248 us | 11.748 us | `0xa6928c4710` | 1.880x | 0.917x | no |
| 8 | 12.218 us | 12.396 us | `0xa1c0b44b77845c` | 1.015x | 0.522x | yes |
| 10 | 19.531 us | 14.081 us | `0xcd308fa1e6b4c086` | 0.721x | 0.413x | yes |
| 12 | 32.260 us | 16.480 us | `0x7a7f97c2c94271b0` | 0.511x | 0.324x | yes |
| 16 | 56.932 us | 22.610 us | `0xee908045efb53b70` | 0.397x | 0.291x | yes |
| 20 | 91.980 us | 30.076 us | `0xf5a298635d1d8fd6` | 0.327x | 0.262x | yes |
| 24 | 137.125 us | 38.474 us | `0x9b50d7bcf01aa6ba` | 0.281x | 0.237x | yes |
| 32 | 255.266 us | 61.581 us | `0xc62750830b41318b` | 0.241x | 0.218x | yes |

The adjusted ratio falls from 0.522x at the first eligible rung (`n=8`) to
0.218x at `n=32`; equivalently, FLINT moves from about 1.9 times faster to 4.6
times faster. This expected divergence reflects FLINT's tuned modular and
asymptotically fast kernels versus Hex's integral Brown recurrence. Because the
comparator is informational, it has no gating-goal verdict.

### Discriminant

The clean fixed-discriminant run at commit
`4423a2c7d9b2565a4f3953b6168c67d48a00e3ae` used:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run \
  $(lake exe hexresultant_bench list | \
    awk '$1 ~ /run(Flint)?Disc[0-9]+$/ {print $1}') \
  --export-file reports/bench-results/hex-resultant-4423a2c7-flint-disc.json
```

The export SHA-256 is
`8e91b3f5a93a5c8960cf6fdab30cc75bb511ca039a0533639ce2a8e29d27526c`.

| n | Hex median | FLINT median | observed hash (both) | raw | adjusted | eligible |
|---:|---:|---:|---:|---:|---:|:---:|
| 4 | 2.404 us | 9.274 us | `0xb1f3fd` | 3.858x | 1.354x | no |
| 6 | 6.746 us | 10.353 us | `0x19be9ab7dc3f` | 1.535x | 0.642x | no |
| 8 | 12.234 us | 11.252 us | `0x37dbc1f675c5f322` | 0.920x | 0.428x | no |
| 10 | 23.092 us | 13.730 us | `0x18872224b5c5ac2a` | 0.595x | 0.334x | yes |
| 12 | 30.684 us | 15.739 us | `0x83c7b0d5b805d6bf` | 0.513x | 0.317x | yes |
| 16 | 62.238 us | 22.513 us | `0xfc6c1ad83c5aa797` | 0.362x | 0.265x | yes |
| 20 | 100.703 us | 30.654 us | `0x777ef2250604a905` | 0.304x | 0.245x | yes |
| 24 | 144.418 us | 39.093 us | `0x5c6e312630af4595` | 0.271x | 0.229x | yes |
| 32 | 280.900 us | 67.281 us | `0x2d5f8d801897b4df` | 0.240x | 0.218x | yes |

The adjusted discriminant ratio likewise declines, from 0.334x at the first
eligible rung (`n=10`) to 0.218x at `n=32`, and approaches the resultant curve
because discriminant is one derivative followed by one resultant. This is the
same expected informational divergence, not a Concern.

## Profile

The single declared input family is both the downstream hot path and the family
with the comparator gap. A representative resultant at `n=32`, deterministic
seed `0xC0FFEE`, was profiled at clean commit
`e0e99a790fa13b4ea05c48eeb7a14ce9235315b7` on `chungus2` (Linux x86-64,
AMD EPYC 9455 48-Core Processor), using LeanBench 0.1.0, Lean 4.33.0-rc1,
samply 0.13.1, and a 999 Hz sampling rate:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexresultant_bench \
  Hex.ResultantBench.runResultant 32 5000000000
```

The raw filtered profile is developer-local at
`/tmp/hex-profile-runResultant-32.json.gz` and is not committed, as required by
`SPEC/profiling.md`. Of 4081 retained samples, flat leaf cost was allocation /
free 68.93%, GMP big-integer arithmetic 20.58%, Lean runtime 4.07%, Hex own
code 0.22%, and other system code 6.20%; the four required categories classify
93.80% of samples.

The inclusive Hex ranking was:

| function | inclusive share |
|---|---:|
| `Hex.DensePoly.resultantOrdered` | 97.40% |
| `Hex.DensePoly.subresultantAux` | 95.22% |
| `Hex.DensePoly.pseudoDivMod` | 73.29% |
| `Hex.DensePoly.divScalarImpl` | 17.13% |
| `Hex.powNat` | 2.55% |
| `Hex.divExp` | 1.89% |

The dominant path is the registered `runResultant` target: ordered resultant
extraction runs the Brown subresultant recurrence, whose pseudo-division loop
creates and discards many arbitrary-precision coefficient values. That explains
both the high allocator leaf share and the GMP multiplication/division share.
No dominant inclusive cost lies outside a registered target.

The filter diagnostics passed every confidence gate:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='hexresultant_bench' tid=369200
calibration:        mode=absolute-monotonic-ms, residual = 2.116 ms (effective limit 5 ms)
regions:            8, total timed = 4104.8 ms
expected samples:   ~4101 on bench thread
retained samples:   4081 on bench thread (7 rejected outside windows)
other-thread noise: 0 samples on non-bench threads within timed windows (informational)
sensitivity +/-5 ms: passed (leaf functions; configured total-variation floor 0.10)
confidence:         passed
```

## Concerns

None.
