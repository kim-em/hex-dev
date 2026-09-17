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
identity. Positive characteristic uses canonical Nat residues and HexMvPoly's
modular operations, interpreted through the shared residue coefficient provider.
Thus `X ^ 3 - X` has generic rank 1 over `MvPolynomial (Fin 1) (ZMod 3)`,
while a field-element goal still requires `x ^ 3 - x ≠ 0`. Literal
`Polynomial.X` goals also support unconditional generic rank. This library
installs no coefficient provider.

See [the SPEC](SPEC/hex-generic-rank-mathlib.md), [tests](Tests.lean), and
[proof measurements](../reports/hex-generic-rank-mathlib-performance.md).
