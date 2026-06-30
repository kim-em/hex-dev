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
Its forward map is `fun M i j => M[(i, j)]` — built on the public entry API, not
on the (now-opaque) backing representation, so the equivalence is unaffected by a
representation change.

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

**Algebraic instances and equivalence upgrades:**
`Hex.Matrix` carries the Mathlib algebraic tower whose operations are the
executable ones (entrywise `+`/`-`/`•` from the `Vector` representation, the
`ofFn` zero/identity, and the executable matrix product). The instances are
transported along `matrixEquiv` (so the laws come from Mathlib's `Matrix`):

```lean
instance [AddCommMonoid R] : AddCommMonoid (Hex.Matrix R n m)
instance [AddCommGroup R]  : AddCommGroup (Hex.Matrix R n m)
instance [Semiring R]      : Module R (Hex.Matrix R n m)
instance [Semiring R]      : Semiring (Hex.Matrix R n n)
instance [Ring R]          : Ring (Hex.Matrix R n n)
instance [CommSemiring R]  : Algebra R (Hex.Matrix R n n)
```

`matrixEquiv` upgrades to the matching bundled equivalences:

```lean
def matrixAddEquiv    [AddCommMonoid R] : Hex.Matrix R n m ≃+ Matrix (Fin n) (Fin m) R
def matrixLinearEquiv [Semiring R]      : Hex.Matrix R n m ≃ₗ[R] Matrix (Fin n) (Fin m) R
def matrixRingEquiv   [Semiring R]      : Hex.Matrix R n n ≃+* Matrix (Fin n) (Fin n) R
def matrixAlgEquiv    [CommSemiring R]  : Hex.Matrix R n n ≃ₐ[R] Matrix (Fin n) (Fin n) R
```

with `@[simp]` transport lemmas (`matrixEquiv_add`, `matrixEquiv_mul`,
`matrixEquiv_smul`, `matrixEquiv_one`, …) feeding `simp`/`grind`.

**Operation correspondence across the equivalence:**
The vector equivalence and the basic container API also cross `matrixEquiv`:

```lean
def vectorEquiv : Vector R n ≃ (Fin n → R)
theorem vectorEquiv_mulVec    : vectorEquiv (M * v) = (matrixEquiv M).mulVec (vectorEquiv v)
theorem matrixEquiv_transpose : matrixEquiv Mᵀ = (matrixEquiv M)ᵀ
theorem matrixEquiv_setRow    : matrixEquiv (setRow M i v) = (matrixEquiv M).updateRow i (vectorEquiv v)
theorem matrixEquiv_setCol    : matrixEquiv (setCol M j v) = (matrixEquiv M).updateCol j v
theorem matrixEquiv_gramMatrix         : matrixEquiv (gramMatrix M) = matrixEquiv M * (matrixEquiv M)ᵀ
theorem matrixEquiv_principalSubmatrix : matrixEquiv (principalSubmatrix M k hk) = (matrixEquiv M).submatrix (Fin.castLE hk) (Fin.castLE hk)
```

(plus `matrixEquiv_takeRows`).
