# Bareiss Dependency Review

Issue #2818 audits whether `Hex.Matrix.bareiss_eq_det` can be removed from
the Mathlib-free core without blocking current consumers.

## Recommendation

Do not reopen #2670 as a removal issue. Supersede it with a narrow design
clarification plus a proof issue that keeps a Mathlib-free Bareiss-to-Leibniz
surface available to `HexGramSchmidt.Int`.

The current split is contradictory for implementation purposes:

- `SPEC/Libraries/hex-matrix.md` says the Bareiss proof lives in
  `hex-matrix-mathlib`.
- `HexGramSchmidt.Int` is Mathlib-free and currently needs
  `Matrix.bareiss_eq_det` to prove public determinant bridge theorems used by
  later Gram-Schmidt and LLL work.
- A Mathlib-layer theorem such as `HexMatrixMathlib.bareissDet_eq_det` cannot be
  imported by `HexGramSchmidt.Int` without reversing the project dependency
  direction.

The safe route is to make the intended ownership explicit, then either:

1. prove `Hex.Matrix.bareiss_eq_det` in the Mathlib-free core, using the local
   Leibniz determinant and existing row-operation lemmas; or
2. redesign the `HexGramSchmidt.Int` proof surface so its Mathlib-free theorems
   no longer need executable Bareiss to agree with `Matrix.det`.

Given the current downstream update proofs, option 1 is the smaller and more
direct route.

## Consumer Classification

### `HexMatrix/Bareiss.lean`

`theorem bareiss_eq_det (M : Matrix Int n n) : bareiss M = det M := by sorry`

Classification: requires either a new Mathlib-free Bareiss theorem or SPEC
clarification. This theorem is not dead code today; removing it breaks
Mathlib-free consumers. The existing proved core surface
`bareiss_eq_bareissData_det` only connects the executable array algorithm to
packaged Bareiss data, not to the Leibniz determinant.

### `HexGramSchmidt/Int.lean`

`scaledCoeffMatrix_bareiss_eq_det` rewrites `Matrix.bareiss_eq_det`.

Classification: requires a Mathlib-free Bareiss theorem. This private bridge is
used by `scaledCoeffRows_lower_eq_coeffs`, which supports the public
`scaledCoeffs_eq` theorem. Replacing it with a Mathlib bridge is not dependency
safe.

`scaledCoeffs_eq_scaledCoeffMatrix_det` calls `Matrix.bareiss_eq_det` directly.

Classification: requires a Mathlib-free Bareiss theorem. This is public
Mathlib-free API connecting executable `scaledCoeffs` to the determinant formula
used by size-reduction update work.

`leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg` rewrites
`Matrix.bareiss_eq_det`.

Classification: requires a Mathlib-free Bareiss theorem unless `gramDet` is
redesigned. The theorem relates the public `Nat` API
`gramDet := (Matrix.bareiss ...).toNat` back to `Matrix.det` under a nonnegative
determinant hypothesis.

`gramDet_rowAdd_earlier` rewrites `Matrix.bareiss_eq_det` twice.

Classification: requires a Mathlib-free Bareiss theorem or a new direct
Mathlib-free Bareiss invariance theorem for the specific row/column update.
The current proof reduces executable `gramDet` equality to `det_rowAdd` and
`det_colAdd`; a bridge-layer theorem cannot be imported here.

### `HexMatrixMathlib/Determinant.lean`

`bareissDet_eq_det` rewrites `Hex.Matrix.bareiss_eq_det`, then applies
`det_eq`.

Classification: belongs only in the Mathlib bridge layer. It should eventually
be proved from the bridge-layer Bareiss proof, but it is not a replacement for
the Mathlib-free core theorem while `HexGramSchmidt.Int` consumes that theorem.

### `HexMatrixMathlib/Determinant/Bareiss.lean`

This file contains substantial bridge-layer Bareiss work:

- `bareissNoPivot_eq_det` proves the no-pivot theorem under
  `NonzeroBareissPivots`;
- singular-branch theorems prove that failed pivot search implies
  `Hex.Matrix.det source = 0`.

Classification: bridge-layer proof infrastructure. It is useful evidence for a
future capstone, but it currently does not expose a full row-pivoted
`Hex.Matrix.bareiss M = Matrix.det (matrixEquiv M)` theorem and cannot be used
from Mathlib-free `HexGramSchmidt.Int`.

## Follow-up Issues

Recommended follow-up titles:

- `HexMatrix: clarify Bareiss determinant proof ownership`
- `HexMatrix: prove Mathlib-free row-pivoted bareiss_eq_det`
- `HexMatrixMathlib: remove bridge-layer dependency on core bareiss_eq_det`

The first issue should decide whether `bareiss_eq_det` is an intentional
Mathlib-free core theorem despite the current SPEC wording. The second should
replace the orphan `sorry` if the answer is yes. The third can then adjust
`HexMatrixMathlib.bareissDet_eq_det` to use its bridge-layer capstone rather
than depending on the core theorem.

## Closure For #2670

#2670 should remain closed. Its removal-oriented scope is stale because the
current project cannot simply delete the core theorem. The replacement work is
not another removal attempt; it is either SPEC clarification plus a core proof,
or a larger redesign of Gram-Schmidt determinant bridges.
