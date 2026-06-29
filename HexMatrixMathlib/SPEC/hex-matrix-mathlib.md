# hex-matrix-mathlib (depends on hex-matrix + Mathlib)

Base Mathlib bridge for the matrix family: proves that our dense matrix type and
its elementary operations correspond to Mathlib's abstract linear algebra.

Mathlib's matrices are function-based and its rank/kernel/span are noncomputable
(cardinals, infima over submodules). This bridge connects our computable
representation to Mathlib's, starting from the matrix equivalence and the
elementary-row-operation dictionary. The row-reduction, determinant, and Bareiss
correspondences build on this base in `HexRowReduceMathlib`,
`HexDeterminantMathlib`, and `HexBareissMathlib` respectively.

**Matrix equivalence:**
```lean
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
```

**Row operations correspond to Mathlib transvections / elementary matrices:**
Our `rowAdd M i j c` is left-multiplication by `Matrix.transvection i j c`; our
`rowSwap` and `rowScale` correspond to Mathlib's `Matrix.swap` permutation matrix
and a diagonal matrix respectively:
```lean
theorem matrixEquiv_rowSwap  (M : Hex.Matrix R n m) (i j : Fin n) : ...
theorem matrixEquiv_rowScale (M : Hex.Matrix R n m) (i : Fin n) (c : R) : ...
theorem matrixEquiv_rowAdd   (M : Hex.Matrix R n m) (src dst : Fin n) (c : R) : ...
```

These give the base dictionary through which the determinant and rank bridges
transfer Mathlib theorems (Cramer's rule, Cayley-Hamilton, rank-nullity,
`diagonal_transvection_induction`) to our matrices.
