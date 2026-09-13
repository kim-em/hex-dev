# Modular integer determinants

Import `HexModularMatrix` for Mathlib-free computation and
`HexModularMatrixMathlib` for the Hadamard bound instance and total correctness.
The contract is [hex-modular-matrix](SPEC/hex-modular-matrix.md).

- `A.detMod?` eliminates below unit pivots over `ZMod64 m`. An all-zero pivot
  column returns `some 0`; a nonzero column without a unit returns `none`.
- `A.detBounded? bound fuel` reconstructs with CRT only after its modulus is
  strictly greater than twice `bound`. Its correctness theorem takes the
  determinant bound as a hypothesis. `A.rowNormBound` supplies a bound with
  an unconditional Mathlib-free proof.
- `A.detModular? fuel` uses the smaller row/column Hadamard bound. Its
  correctness theorem takes `LawfulDetBound`, supplied by the companion.
- `Hex.ModularMatrix.detWith A fuel` records the modular attempt and any
  Bareiss fallback. `Hex.ModularMatrix.det A` chooses capped adaptive fuel
  and returns the integer result. Finite prime supply cannot make it partial.

This implements the one-image and determinant milestones. The seeded divisor
route, Dixon solves, rank and kernel APIs belong to later milestones. In
particular, `detWith` currently takes only the matrix and fuel; it has no
inactive seed or divisor flag.

The conformance fixtures cover singular and empty matrices, nonunit pivots,
bad initial primes, large entries and forced fallback. The benchmark target
`hexmodularmatrix_bench` compares the bounded modular route, Bareiss and
FLINT on identical structured, dense random and unimodular inputs. Its
`verify` command runs three small CI anchors; the full comparator ladder is
collected by `scripts/bench/modmat_flint.py` on the shared host.
The [baseline report](../reports/hex-modular-matrix-performance.md) records
timings, capped calls, comparator errors and the subsequent corrected runs.

The default fuel cap is 16384 primes below 2³¹. A Hadamard bound of at least
2⁵⁰⁷⁹⁰³ therefore cannot be reconstructed within that budget and reaches
Bareiss fallback. The baseline also includes two evaluations of the Hadamard
bound in the default route and the relocated square-root routine's conservative
Newton starting value. Bound reuse, square-root initialization and elimination
buffer specialization remain opportunities for performance work.
