# HexGenericRankMathlib

Import `HexGenericRankMathlib` to add symbolic expressions to the `rank` tactic.
For example, `rank` proves `!![x, 1; 1, x].rank = 2` with the remaining condition
`x ^ 2 - 1 ≠ 0`, or closes immediately when that hypothesis is available.
Upper bounds need no condition. Polynomial-ring goals with independent `X`
atoms have an unconditional generic rank.

`generic_rank% A` returns the reified polynomial matrix, its checked certificate,
its generic rank and the interpretation back into `A`. `rank% A` returns an
actual rank equality and declines when its nonvanishing condition is unresolved.
The programmatic provider retains the sealed atom environment for `rank_locus`.

The kernel checks canonical polynomial lists using the shared HexMvPoly
arithmetic. It never evaluates the certificate producer or a Hex.Matrix
identity. The finite-field fallback checks integer representatives modulo the
characteristic, using the same integer list arithmetic. The dedicated canonical
Nat residue encoding is pending #10257; the positive-characteristic output-1
probe is reserved for that representation and remains a documented non-test
per #10223, although the integer fallback can already prove its goal. No coefficient
provider is installed by this library.

See [the SPEC](SPEC/hex-generic-rank-mathlib.md), [tests](Tests.lean), and
[proof measurements](../reports/hex-generic-rank-mathlib-performance.md).
