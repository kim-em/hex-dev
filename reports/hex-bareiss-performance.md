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
python-flint driver, per `SPEC/Libraries/hex-bareiss.md §"External comparators"`
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

## Comparator Ratios

Input family `structured-bareiss-determinant`, declared complexity `n³`. Hex's
row-pivoted Bareiss fraction-free elimination against FLINT's multimodular
reduction + CRT determinant on the same deterministic tridiagonal fixture. The
`adjusted ratio` subtracts the ~55.2 ms persistent-subprocess startup overhead
from the FLINT median when positive, then divides by the Hex median; a rung is
**eligible** when that overhead is at most 50% of measured FLINT wall time and
per-call wall time is at most the 10 s hard ceiling.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 75.315 µs | 51.750 ms | 687.118x | 0.000x | no |
| 24 | 274.823 µs | 51.305 ms | 186.685x | 0.000x | no |
| 32 | 687.666 µs | 51.755 ms | 75.260x | 0.000x | no |
| 48 | 2.483 ms | 52.133 ms | 21.000x | 0.000x | no |
| 64 | 6.343 ms | 52.556 ms | 8.286x | 0.000x | no |
| 96 | 24.315 ms | 56.703 ms | 2.332x | 0.061x | no |
| 128 | 59.993 ms | 58.395 ms | 0.973x | 0.053x | no |
| 192 | 211.724 ms | 70.594 ms | 0.333x | 0.073x | no |
| 256 | 520.158 ms | 88.929 ms | 0.171x | 0.065x | no |
| 320 | 1.035 s | 114.064 ms | 0.110x | 0.057x | yes |
| 384 | 1.816 s | 149.450 ms | 0.082x | 0.052x | yes |
| 512 | 4.388 s | 270.629 ms | 0.062x | 0.049x | yes |

Trend: the raw ratio falls monotonically from 687x at `n = 16` (Hex fast, FLINT
dominated by the ~55 ms startup floor) through unity at `n = 128` to 0.062x at
`n = 512`. Within the eligible rungs (`n = 320, 384, 512`) the adjusted ratio is
roughly flat at `0.049x – 0.057x` with a slow drift toward FLINT pulling ahead:
once driver startup is subtracted, FLINT spends about 5% of Hex's wall time on
the same determinant surface, widening as `n` grows. This is the structural gap
named in advance by the `informational` rationale (FLINT uses multimodular
reduction + CRT; Hex uses Bareiss fraction-free elimination). The comparator is
`informational`, so the divergence is recorded for orientation rather than as a
Phase-4 gate.

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

- The FLINT `fmpz_mat.det` comparator pulls steadily ahead of `runBareissDet`
  across the ladder: raw ratio `0.973x → 0.062x` from `n = 128` to `n = 512`,
  and within the eligible range the adjusted ratio drifts from `0.057x` to
  `0.049x` — FLINT spends roughly 5% of Hex's wall time on the same surface, and
  the gap widens with `n`. The comparator is `informational`, so this is
  recorded for orientation rather than as a Phase-4 gate; the structural gap
  matches the rationale (FLINT multimodular reduction + CRT versus Hex's
  fraction-free Bareiss elimination over `Int`). A follow-up may file a narrow
  issue against `Hex.Matrix.bareiss` if a faster determinant surface is wanted
  (for instance, a multimodular CRT path layered over the existing Bareiss
  kernel as a Tier-2 fast path).
