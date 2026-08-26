# HexResultant Performance Report

## Bench Targets

The four parametric registrations in `bench/HexResultant/Bench.lean` use these
declared complexity expressions, copied from their registration sites:

- `Hex.ResultantBench.runPseudoDiv`: `n * n * n`
- `Hex.ResultantBench.runChain`: `wallCostModel n`
- `Hex.ResultantBench.runResultant`: `wallCostModel n`
- `Hex.ResultantBench.runDisc`: `wallCostModel n`

Here `wallCostModel n` is defined adjacent to the registrations as
`n * n * (Nat.log2 (n + 1) + 1)`. The seed-`0xC0FFEE`
`bounded-dense-equal-degree-prs` family uses equal-degree pairs at
`#[4, 6, 8, 10, 12, 16, 20, 24, 32]` for Brown chains, resultants, and
discriminants. The separate `bounded-dense-pseudo-division` family uses a
degree-`n` dividend and degree-`n / 2` divisor, both with leading coefficient
two, at `#[24, 32, 40, 48, 64, 80, 96, 128]`.

The resultant and discriminant ladders also have one fixed Hex registration and
one fixed FLINT registration per rung. `runFlintOverhead` is an auxiliary fixed
registration for persistent-driver protocol calibration; it has no polynomial
work and makes no algorithmic-complexity claim. The fixed-rung input values are
prepared during module initialization, outside the measured child region.

## Verdicts

The scientific run used LeanBench 0.1.0 and Lean 4.33.0-rc1 on clean commit
`82db24dbe7dadd232eeb8964ab09dc74deaa9e9e`, host `chungus2` (Linux x86-64,
AMD EPYC 9455 48-Core Processor), with three outer trials per rung:

```sh
lake exe hexresultant_bench run \
  Hex.ResultantBench.runPseudoDiv Hex.ResultantBench.runChain \
  Hex.ResultantBench.runResultant Hex.ResultantBench.runDisc \
  --outer-trials 3 \
  --export-file reports/bench-results/hex-resultant-82db24db-scientific.json
```

The export is
`reports/bench-results/hex-resultant-82db24db-scientific.json`, SHA-256
`1cd5fc45a94a5717d9a0a30665efd3bee5d9f6bcd72a6ac72ad2102886b33a79`.
Every rung was above the configured signal floor and participated in its
verdict.

- `runPseudoDiv`: consistent with declared complexity (`beta=-0.253`,
  `cMin=0.279`, `cMax=0.637`).
- `runChain`: consistent with declared complexity (`beta=+0.116`,
  `cMin=42.925`, `cMax=56.893`).
- `runResultant`: consistent with declared complexity (`beta=-0.015`,
  `cMin=40.724`, `cMax=52.257`).
- `runDisc`: consistent with declared complexity (`beta=+0.008`,
  `cMin=40.925`, `cMax=53.249`).

The fixed runs used five measured repeats with at least 0.2 s of auto-tuned
inner repetitions per child. The tables in Comparator Ratios enumerate the
median of every fixed registration. The Hex and FLINT observed hashes agree at
every one of the 18 paired rungs. Smoke verification after adding the overhead
probe also passed all 41 registrations:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench verify
```

The 41-target verification completed in 0.781 s on the report host, well below
the 30 s per-library warning and 360 s repository-wide hard cap.

## Comparator Ratios

The SPEC and `libraries.yml` classify
`FLINT fmpz_poly resultant/discriminant via python-flint` as informational.
The implementation uses python-flint 0.9.0 and the shared persistent JSON-line
driver; FLINT/PARI correctness remains independently checked by the Resultant
conformance oracle.

The constant steady-state framing floor was measured with the no-work
`fmpz_poly.overhead` request at clean commit
`b29b3e9494f80ce00c971fc7aea7494d70349838` on the same host:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run Hex.ResultantBench.runFlintOverhead \
  --repeats 11 --min-total-seconds 0.5 \
  --export-file reports/bench-results/hex-resultant-b29b3e94-flint-overhead.json
```

The median was **6.120 us** per request/reply (minimum 5.916 us, maximum
6.277 us), with 131072 warm requests in each outer repeat. The export is
`reports/bench-results/hex-resultant-b29b3e94-flint-overhead.json`, SHA-256
`b8eaaeaf94b84e7ada5bf2885c971f487c860ef4d3f57ce483ad5b82b593a25f`.
This no-work request measures only the constant JSON-line framing and dispatch
floor. Per-rung coefficient encoding, JSON parsing, and `fmpz_poly`
construction are not subtracted, so adjusted FLINT times below are conservative
upper bounds on its algorithm time.
Every comparator median below has more than 5% protocol overhead, so each table
shows both `raw = FLINT / Hex` and
`adjusted = (FLINT - 6.120 us) / Hex`. Eligibility means that overhead is at
most 50% of the FLINT median and the call is below the 10 s ceiling.

### Resultant

The clean fixed-resultant run at commit
`731e5689cb9e86eb3c81cd7732cd354f341d2d24` used:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run \
  $(lake exe hexresultant_bench list | \
    awk '$1 ~ /run(Flint)?Resultant[0-9]+$/ {print $1}') \
  --export-file reports/bench-results/hex-resultant-731e5689-flint-resultant.json
```

The export SHA-256 is
`499aeea0cbf7f9238dae17a2d6379673af152428409c318b5b0d235fc339a3ff`.

| n | Hex median | FLINT median | observed hash (both) | raw | adjusted | eligible |
|---:|---:|---:|---:|---:|---:|:---:|
| 4 | 1.646 us | 9.227 us | `0x4333fb` | 5.606x | 1.888x | no |
| 6 | 4.987 us | 9.714 us | `0xa6928c4710` | 1.948x | 0.721x | no |
| 8 | 10.598 us | 11.334 us | `0xa1c0b44b77845c` | 1.069x | 0.492x | no |
| 10 | 17.621 us | 12.823 us | `0xcd308fa1e6b4c086` | 0.728x | 0.380x | yes |
| 12 | 30.199 us | 14.795 us | `0x7a7f97c2c94271b0` | 0.490x | 0.287x | yes |
| 16 | 55.217 us | 19.942 us | `0xee908045efb53b70` | 0.361x | 0.250x | yes |
| 20 | 89.797 us | 26.996 us | `0xf5a298635d1d8fd6` | 0.301x | 0.232x | yes |
| 24 | 134.362 us | 34.898 us | `0x9b50d7bcf01aa6ba` | 0.260x | 0.214x | yes |
| 32 | 254.961 us | 57.767 us | `0xc62750830b41318b` | 0.227x | 0.203x | yes |

The adjusted ratio falls from 0.380x at the first eligible rung (`n=10`) to
0.203x at `n=32`; equivalently, FLINT moves from about 2.6 times faster to 4.9
times faster. This expected divergence reflects FLINT's tuned modular and
asymptotically fast kernels versus Hex's integral Brown recurrence. Because the
comparator is informational, it has no gating-goal verdict.

### Discriminant

The clean fixed-discriminant run at commit
`cb08a5100421685ad208384557635f71592076a8` used:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexresultant-bench-venv/bin/python \
  lake exe hexresultant_bench run \
  $(lake exe hexresultant_bench list | \
    awk '$1 ~ /run(Flint)?Disc[0-9]+$/ {print $1}') \
  --export-file reports/bench-results/hex-resultant-cb08a510-flint-disc.json
```

The export SHA-256 is
`2f0660ee5949209a5c573d995141369869688a207f0e36e39581cacb51a3999d`.

| n | Hex median | FLINT median | observed hash (both) | raw | adjusted | eligible |
|---:|---:|---:|---:|---:|---:|:---:|
| 4 | 1.502 us | 7.941 us | `0xb1f3fd` | 5.287x | 1.212x | no |
| 6 | 5.368 us | 9.065 us | `0x19be9ab7dc3f` | 1.689x | 0.549x | no |
| 8 | 10.637 us | 10.051 us | `0x37dbc1f675c5f322` | 0.945x | 0.370x | no |
| 10 | 21.517 us | 12.384 us | `0x18872224b5c5ac2a` | 0.576x | 0.291x | yes |
| 12 | 28.534 us | 13.996 us | `0x83c7b0d5b805d6bf` | 0.491x | 0.276x | yes |
| 16 | 59.954 us | 20.030 us | `0xfc6c1ad83c5aa797` | 0.334x | 0.232x | yes |
| 20 | 98.431 us | 27.664 us | `0x777ef2250604a905` | 0.281x | 0.219x | yes |
| 24 | 142.047 us | 35.853 us | `0x5c6e312630af4595` | 0.252x | 0.209x | yes |
| 32 | 284.360 us | 62.824 us | `0x2d5f8d801897b4df` | 0.221x | 0.199x | yes |

The adjusted discriminant ratio likewise declines, from 0.291x at the first
eligible rung (`n=10`) to 0.199x at `n=32`, and approaches the resultant curve
because discriminant is one derivative followed by one resultant. This is the
same expected informational divergence, not a Concern.

## Profile

The two declared compiled input families each have one representative profile.
The equal-degree family is the downstream hot path and has the worst measured
comparator gap; the pseudo-division case separately covers its degree-`n` by
degree-`n / 2` geometry.

### Equal-degree Brown/resultant family

A representative resultant at `n=32`, deterministic seed `0xC0FFEE`, was
profiled at clean commit
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

### Pseudo-division family

The degree-128 member of `bounded-dense-pseudo-division`, with a degree-64
divisor and both leading coefficients fixed at two, was profiled at clean
commit `60578d9b5f4d3431f83d20b32ff3eea3e4675c13` on the same host and toolchain:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexresultant_bench \
  Hex.ResultantBench.runPseudoDiv 128 5000000000
```

The raw filtered profile is developer-local at
`/tmp/hex-profile-runPseudoDiv-128.json.gz`. Of 4761 retained samples, flat
leaf cost was allocation / free 69.06%, GMP big-integer arithmetic 19.20%,
Lean runtime 4.03%, Hex own code 0.00%, and other system code 7.71%; the four
required categories classify 92.29% of samples.

The inclusive Hex ranking was:

| function | inclusive share |
|---|---:|
| `Hex.ResultantBench.runPseudoDiv` | 99.31% |
| `Hex.DensePoly.pseudoDivMod` | 93.59% |

The registered pseudo-division target dominates the profile directly. Its
array fold repeatedly constructs arbitrary-precision quotient and remainder
coefficients, accounting for the allocator and GMP leaf shares; no dominant
inclusive cost lies outside a registered target.

The second profile also passed every confidence gate:

```text
=== lean-bench-samply filter diagnostics ===
bench thread:       name='hexresultant_bench' tid=718398
calibration:        mode=absolute-monotonic-ms, residual = 0.995 ms (effective limit 5 ms)
regions:            7, total timed = 4780.0 ms
expected samples:   ~4775 on bench thread
retained samples:   4761 on bench thread (7 rejected outside windows)
other-thread noise: 0 samples on non-bench threads within timed windows (informational)
sensitivity +/-5 ms: passed (leaf functions; configured total-variation floor 0.10)
confidence:         passed
```

## Concerns

None.
