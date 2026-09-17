# hex-modular-matrix-mathlib

This correspondence layer supplies the determinant, solve and rank parts of the companion in
[hex-modular-matrix](../../HexModularMatrix/SPEC/hex-modular-matrix.md).

`Bound.lean` constructs `Hex.Matrix.LawfulDetBound` from the real Hadamard
inequality in `HexMatrixMathlib.Hadamard`, applying the column inequality to
the matrix and its transpose. Integer square roots and bound computation
remain in the Mathlib-free layer.

`Det.lean` proves `HexModularMatrixMathlib.detWith_eq`, `det_eq`, and
`detViaDivisor_eq`, including the seeded divisor route and exhaustion through
`HexMatrixMathlib.bareiss_eq_det`. The total divisor wrapper selects Bareiss
below the measured crossover. The decidable instance for `A.det = 0` uses the
ordinary modular determinant and transports its answer through `det_eq`;
`Hex.Det` retains its independent dispatch policy.

`Solve.lean` identifies checked integer numerator/denominator pairs with
Mathlib rational `Matrix.mulVec` solutions and the nonsingular inverse.
`solveMat_eq` transports simultaneous right-hand sides, and `solveWitness_eq`
gives both the rational equation and nonzero determinant for a returned witness.
Default-budget existence uses the core completeness theorems and the supplied
Hadamard instance, with the explicit lower bound on supply primes retained.

`Rank.lean` reuses hex-rank-mathlib's rank soundness and integer fallback
agreement. `kernel_independent` reads the negative identity free block;
`kernel_span` combines annihilation, independence and rank-nullity to identify
the full rational kernel. Rank equality decidability is imported from
hex-rank-mathlib without a second instance.

## Validation ownership

This is a `correspondence_only: true` library, with comparator absence class
**correspondence-only-layer**. It defines proofs and transports executable
decidability; it owns no independent benchmark algorithm.

Computational conformance owners: `HexModularMatrix`.
Computational performance owners: `HexModularMatrix`.

The default Lake build checks all companion modules and their dependencies.
