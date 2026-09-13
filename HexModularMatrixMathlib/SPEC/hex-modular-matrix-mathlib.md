# hex-modular-matrix-mathlib

This correspondence layer supplies the determinant half of the companion in
[hex-modular-matrix](../../HexModularMatrix/SPEC/hex-modular-matrix.md).

`Bound.lean` constructs `Hex.Matrix.LawfulDetBound` from the real Hadamard
inequality in `HexMatrixMathlib.Hadamard`, applying the column inequality to
the matrix and its transpose. Integer square roots and bound computation
remain in the Mathlib-free layer.

`Det.lean` proves `HexModularMatrixMathlib.detWith_eq` and `det_eq`, including the
exhaustion route through `HexMatrixMathlib.bareiss_eq_det`. Its decidable
instance for `A.det = 0` computes the total determinant and transports the
answer through the correctness theorem. Importing this companion deliberately
selects its modular dispatcher for decidability, so the proved route remains
usable from Mathlib before a crossover is established. The baseline currently
favors Bareiss; this instance replaces Mathlib’s permutation enumeration, while
the general `Hex.Det` dispatcher retains its independent Bareiss policy.

The milestone-2 dispatcher takes a matrix and fuel. The divisor and seeded
dispatcher extension belongs to the subsequent Dixon/divisor milestone.

## Validation ownership

This is a `correspondence_only: true` library, with comparator absence class
**correspondence-only-layer**. It defines proofs and transports executable
decidability; it owns no independent benchmark algorithm.

Computational conformance owners: `HexModularMatrix`.
Computational performance owners: `HexModularMatrix`.

The default Lake build checks both companion modules and their dependencies.
