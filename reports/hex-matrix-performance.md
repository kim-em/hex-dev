# HexMatrix Performance Report

`HexMatrix` is the dense base of the matrix family (constructors, accessors,
vector helpers, dot product, dense matrix algebra, elementary row/column
operations, submatrix, Gram). The determinant, Bareiss, and row-reduction
Phase-4 surfaces live in `reports/hex-determinant-performance.md`,
`reports/hex-bareiss-performance.md`, and
`reports/hex-row-reduce-performance.md`.

## Bench Targets

- `Hex.MatrixBench.runSquareMulChecksum`: `n * n * n`

The dense base surfaces (multiplication, row operations on the structural
`Vector` / `Array` primitives) have no named external comparator: they declare
absence with the `structural-layer` reason per
`SPEC/Libraries/hex-matrix.md §"External comparators"`.

## Verdicts

Measured on `carica` (Apple M2 Ultra, macOS 14.6.1); the
`dense-square-multiplication` figures below were captured under the
pre-split consolidated `hexmatrix_bench` driver and are unchanged by the
library split (the timed `Hex.Matrix.mul` surface is identical).

- `Hex.MatrixBench.runSquareMulChecksum`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runSquareMulChecksum`
  - Input family: `dense-square-multiplication`; deterministic salts `17` and
    `43`; parameters `160, 192, 224, 256`.
  - Per-call times: `442.607 ms`, `763.753 ms`, `1.210 s`, `1.833 s`.
  - Verdict: consistent with declared complexity (`cMin=107.634`,
    `cMax=109.279`, `β=—`).

Smoke wiring was also checked with `lake exe hexmatrix_bench list` and
`lake exe hexmatrix_bench verify`.

## Profile

Profile captured on `carica` through the bench-timed-region filtering wrapper
(`scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench <target>
<param> 5000000000`, `samply 0.13.1` at 999 Hz).

- `dense-square-multiplication`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench Hex.MatrixBench.runSquareMulChecksum 160 5000000000`
  - Leaf cost: allocation/free 55.3%, Lean runtime and harness 24.7%,
    GMP big-integer arithmetic 15.1%, Lean own code 3.1%, other system
    samples 1.8%.
  - Inclusive ranking: `Hex.MatrixBench.runSquareMulChecksum` and its
    benchmark wrapper covered 100.0% of retained samples,
    `Hex.Matrix.mul` specialised for the target covered 99.1%,
    `Hex.Vector.dotProduct` covered 93.8%, and the inner dot-product fold
    covered 82.0%. The high allocator/GMP leaf cost is attributable to the
    boxed `Int` matrix multiplication surface.

The dominant inclusive costs all map to the registered `HexMatrix.Bench`
target. No unattributed dominant cost was observed.

## Concerns

None for the dense base surface.
