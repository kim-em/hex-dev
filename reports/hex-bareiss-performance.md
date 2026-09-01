# HexBareiss Performance Report

`HexBareiss` provides the executable fraction-free Bareiss determinant over
`Int` and its bordered-minor support. Its Phase-4 surface is the row-pivoted
Bareiss determinant `Hex.Matrix.bareiss`, paired with the FLINT `fmpz_mat.det`
informational comparator.

## Bench Targets

- `Hex.BareissBench.runBareissDet`: `n * n * n`

Paired Hex/FLINT informational comparator fixed registrations:
`runBareissDet{16,24,32,48,64,96,128,192,256,320,384,512}` ↔
`runFlintBareissDet{…}` (`fmpz_mat.det` via the shared persistent-subprocess
python-flint driver, per `HexBareiss/SPEC/hex-bareiss.md §"External comparators"`
and `SPEC/benchmarking.md §"External comparators" §"Process call"`). The named
comparator is `FLINT fmpz_mat_det via python-flint` (matching
`libraries.yml: HexBareiss.phase4.comparators[0].tool`).

## Verdicts

Measured on `carica` (Apple M2 Ultra, macOS 14.6.1). The
`structured-bareiss-determinant` figures below were captured under the
pre-split consolidated `hexmatrix_bench` driver and are unchanged by the
library split (the timed `Hex.Matrix.bareiss` surface is identical).

- `Hex.BareissBench.runBareissDet`
  - Command: `lake exe hexbareiss_bench run Hex.BareissBench.runBareissDet`
  - Input family: `structured-bareiss-determinant`; deterministic salt `71`;
    parameters `8, 12, 16`.
  - Per-call times: `9.136 µs`, `28.275 µs`, `72.236 µs`.
  - Verdict: consistent with declared complexity (`cMin=16.363`,
    `cMax=17.846`, `β=—`).

The 24 paired Hex / FLINT fixed-comparator registrations passed — each Hex
target and its paired FLINT call returned the same observed hash at every rung,
covering both the magnitude and the sign of the determinant (Hex's row-pivoted
Bareiss tracks the swap permutation parity; FLINT's multimodular CRT returns the
signed determinant in the same convention).

### Generic-coefficient regression gate

The generic coefficient implementation retains `bareiss` as an `Int`
specialization of `bareissWith`. The specialization annotations propagate the
fixed exact quotient into the inner loop: generated C for the benchmark calls
`lean_int_div_exact` directly and contains no closure application at the
division site.

Five-repeat medians on the same deterministic
`structured-bareiss-determinant` inputs compared this branch with
`origin/main` (`32ac5850a`). The observed determinant hashes agreed.

| n | `origin/main` | generic branch | branch/base | limit |
|---:|---:|---:|---:|---:|
| 256 | 263.939 ms | 148.041 ms | 0.561x | 1.02x |
| 384 | 825.551 ms | 512.178 ms | 0.620x | 1.02x |

Both required rungs pass the no-regression ceiling.

The SPEC's same-binary A/B comparison measures the retained `bareiss` entry
against `bareissWith Hex.exactDiv`. Five repeats were pinned to verified-idle
CPU 2 on `chungus2`; output hashes agreed at both rungs.

| n | direct `Int` specialization | `bareissWith Hex.exactDiv` | generic/direct |
|---:|---:|---:|---:|
| 256 | 150.466 ms | 259.076 ms | 1.722x |
| 384 | 523.082 ms | 919.823 ms | 1.758x |

`Hex.exactDiv` is the guarded quotient derived from ordinary integer division,
whereas the retained specialization reaches `lean_int_div_exact` directly.
The A/B result records the material reason the direct-call code-generation
check is part of the no-regression gate.

## Comparator Ratios

Input family `structured-bareiss-determinant`, declared complexity `n³`. Hex's
row-pivoted Bareiss fraction-free elimination against FLINT's multimodular
reduction + CRT determinant on the same deterministic tridiagonal fixture.

The paired registrations were rerun from clean commit
`f4f013c638460c621728e108c9b77988df8d2836` on `chungus2` (AMD EPYC
9455, Linux x86_64), pinned to CPU 2:

```sh
PATH=/tmp/hex-9804-flint/bin:$PATH
lake exe hexbareiss_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 2 lake exe hexbareiss_bench run \
    --export-file reports/bench-results/hex-bareiss-f4f013c-issue9804-warmed.json
```

The export contains 27 fixed registrations and 135 successful outer repeats.
All registrations have internally stable hashes and all 12 Hex/FLINT pairs
agree on their observed hash. Its SHA-256 is
`f3840dc9a2dec0dce85172f72330aa37bddb94eaebadd7ee078b4d55eb6716e1`.

Both arms discard a first warmup call, so one-time interpreter/python-flint
startup is excluded from all timed medians. The registered synchronous
`runFlintOverhead` case measures the steady-state trivial-request round trip at
6.115 µs in the same artifact. Startup and steady-state overhead are therefore
separate: startup is represented only by the discarded warmup, while the
reported overhead is the reusable process-call floor. An adjusted ratio is
shown where this floor exceeds 5% of the FLINT median. Every retained rung is
below the 10 s hard ceiling and the overhead is below 50% of the FLINT median,
so all 12 pairs are eligible.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 25.841 µs | 50.393 µs | 1.950x | 1.713x | yes |
| 24 | 87.028 µs | 108.204 µs | 1.243x | 1.173x | yes |
| 32 | 207.809 µs | 173.796 µs | 0.836x | — | yes |
| 48 | 757.016 µs | 417.884 µs | 0.552x | — | yes |
| 64 | 1.927 ms | 1.037 ms | 0.538x | — | yes |
| 96 | 7.061 ms | 2.485 ms | 0.352x | — | yes |
| 128 | 17.611 ms | 4.897 ms | 0.278x | — | yes |
| 192 | 61.683 ms | 12.477 ms | 0.202x | — | yes |
| 256 | 150.128 ms | 25.542 ms | 0.170x | — | yes |
| 320 | 299.955 ms | 42.737 ms | 0.142x | — | yes |
| 384 | 522.987 ms | 67.725 ms | 0.129x | — | yes |
| 512 | 1.252 s | 145.195 ms | 0.116x | — | yes |

The warmed curve crosses unity between `n = 24` and `n = 32`, then the ratio
falls from 0.836x to 0.116x through the remaining ten rungs. This is the
structural gap named in advance by the `informational` rationale (FLINT uses
multimodular reduction + CRT; Hex uses Bareiss fraction-free elimination). The
comparator is
`informational`, so this expected different-complexity-class divergence is
recorded for optimization orientation rather than as a Phase-4 gate or an
evidence defect. HexBareiss claims the specified fraction-free algorithm; a
faster multimodular determinant would be a distinct optional surface, not a
repair required by this report.

## Profile

Profile captured on `carica` through the bench-timed-region filtering wrapper.

- `structured-bareiss-determinant`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexbareiss_bench Hex.BareissBench.runBareissDet 16 5000000000`
  - Leaf cost: Lean runtime and harness 57.8%, Lean own code 22.6%,
    allocation/free 13.5%, GMP big-integer arithmetic 5.5%, other system
    samples 0.6%.
  - Inclusive ranking: `Hex.Matrix.bareiss` covered 95.8% of retained samples,
    `bareissArrayState` 95.6%, `pivotLoop` 92.5%, `stepMatrix` 42.9% boxed /
    36.5% unboxed, `exactDiv` 8.1%. These dominant entries are the row-pivoted
    Bareiss determinant path measured by the registered `runBareissDet` target.

The dominant inclusive costs all map to the registered `HexBareiss.Bench`
target. No unattributed dominant cost was observed.

## Concerns
