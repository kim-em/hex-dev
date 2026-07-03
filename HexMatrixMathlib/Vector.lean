/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrixMathlib.Basic

public section

/-!
The executable-`Vector` ↔ Mathlib-`Fin n → R` equivalence, the fold-to-`Finset.sum`
bridge for dot products, and the matrix-vector-product correspondence.

These are the base facts through which the row-span, rank, and nullspace bridges
(in `HexRowReduceMathlib`) and the lattice bridges (in `HexLLLMathlib`) move
between the two vector representations.
-/

open Matrix

namespace HexMatrixMathlib

universe u

variable {R : Type u} {n m : Nat}

/-- Convert an executable `Vector` into Mathlib's function representation. -/
@[expose]
def vectorEquiv : Vector R n ≃ (Fin n → R) where
  toFun := fun v i => v[i]
  invFun := Vector.ofFn
  left_inv := by
    intro v
    ext i
    simp
  right_inv := by
    intro f
    funext i
    simp

/-- `vectorEquiv v` has entry `v[i]` at `i`, so a caller can rewrite
`vectorEquiv v i` to `v[i]` without unfolding it. -/
@[simp, grind =] theorem vectorEquiv_apply (v : Vector R n) (i : Fin n) :
    vectorEquiv v i = v[i] :=
  rfl

/-- The inverse direction of `vectorEquiv` materialises a function as an
executable vector entrywise: `(vectorEquiv.symm f)[i]` is just `f i`. -/
@[simp, grind =] theorem vectorEquiv_symm_apply (f : Fin n → R) (i : Fin n) :
    (vectorEquiv.symm f)[(i : Nat)] = f i := by
  simp [vectorEquiv]

/-- A left fold of `(· + f ·)` over `List.finRange n` from `0` is the finite sum
`∑ i, f i`; the bridge from the executable fold-sum to Mathlib's `Finset.sum`. -/
theorem foldl_finRange_eq_sum [AddCommMonoid R] (f : Fin n → R) :
    (List.finRange n).foldl (fun acc i => acc + f i) 0 = ∑ i, f i := by
  rw [← List.foldl_map]
  rw [← List.sum_eq_foldl]
  rw [← List.sum_toFinset f (List.nodup_finRange n)]
  rw [List.toFinset_finRange]

/-- The executable dot product equals Mathlib's `dotProduct` of the two vectors
read through `vectorEquiv`. -/
theorem dotProduct_eq [NonUnitalNonAssocSemiring R] (u v : Vector R n) :
    u.dotProduct v = dotProduct (vectorEquiv u) (vectorEquiv v) := by
  unfold Vector.dotProduct dotProduct
  rw [foldl_finRange_eq_sum]
  rfl

/-- Row `i` of the Mathlib matrix `matrixEquiv M` is the image under `vectorEquiv`
of the executable row `Hex.Matrix.row M i`, letting span/rank lemmas pass between
the two row representations. -/
@[simp, grind =] theorem matrixEquiv_row (M : Hex.Matrix R n m) (i : Fin n) :
    _root_.Matrix.row (matrixEquiv M) i = vectorEquiv (Hex.Matrix.row M i) := by
  funext j
  simp [Hex.Matrix.row]

/-- Column `j` of the Mathlib matrix `matrixEquiv M` is the image under
`vectorEquiv` of the executable column `Hex.Matrix.col M j`. -/
@[simp, grind =] theorem matrixEquiv_col (M : Hex.Matrix R n m) (j : Fin m) :
    _root_.Matrix.col (matrixEquiv M) j = vectorEquiv (Hex.Matrix.col M j) := by
  funext i
  simp [Hex.Matrix.col]

/-- The executable matrix-vector product transports to Mathlib's `Matrix.mulVec`
under `matrixEquiv`/`vectorEquiv`. -/
theorem vectorEquiv_mulVec [Semiring R] (M : Hex.Matrix R n m) (v : Vector R m) :
    vectorEquiv (M * v) = (matrixEquiv M).mulVec (vectorEquiv v) := by
  funext i
  simp only [vectorEquiv_apply]
  change (Hex.Matrix.mulVec M v)[i.val] = (matrixEquiv M).mulVec (vectorEquiv v) i
  unfold Hex.Matrix.mulVec Hex.Matrix.row Vector.dotProduct
  rw [Vector.getElem_ofFn i.isLt]
  rw [foldl_finRange_eq_sum]
  unfold _root_.Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k _
  rfl

end HexMatrixMathlib
