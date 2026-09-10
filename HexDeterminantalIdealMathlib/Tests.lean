/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexDeterminantalIdealMathlib
public import HexMatrixMathlib

public section

/-!
Build-only transport checks: the headline theorem applied to a closed integer
matrix through `Int.castRingHom ℚ`, the locus corollary applied to the `2 × 2`
Vandermonde matrix at a point on and a point off the diagonal, and the
invariance theorem with its hypotheses in the form a consumer has. These are
not an independent oracle; the SymPy stream of `HexDeterminantalIdeal` is.

The closed minors are read off with `det_two_by_two` after the tuple
enumeration is evaluated by `decide +kernel`; the Leibniz sum itself is not
kernel-evaluated here, because `permutationVectors` goes through core
`Vector.map`, which the kernel cannot unfold from a `module` file.
-/

namespace HexDeterminantalIdealMathlib.Tests

open HexMatrixMathlib Hex.Matrix

/- The theorems are stated over a Mathlib `Field`, whose `Lean.Grind.Field`
instance is `Field.toGrindField`; prefer it over the built-in instance for `ℚ`
so that the closed examples elaborate with the instance the theorems use. -/
attribute [local instance 2000] Field.toGrindField CommRing.toGrindCommRing

/-- The strictly increasing pairs in `Fin 2` and in `Fin 3`. -/
theorem selectedColumnTuples_two_two : selectedColumnTuples 2 2 = [#v[0, 1]] := rfl

theorem selectedColumnTuples_two_three :
    selectedColumnTuples 2 3 = [#v[0, 1], #v[0, 2], #v[1, 2]] := rfl

/-- `[[1, 2, 3], [4, 5, 7]]`, of rank `2`. -/
def A23 : Hex.Matrix Int 2 3 :=
  Hex.Matrix.ofFn fun i j =>
    if i.val = 0 then (if j.val = 0 then 1 else if j.val = 1 then 2 else 3)
    else (if j.val = 0 then 4 else if j.val = 1 then 5 else 7)

/-- The three `2 × 2` minors of `A23`. -/
theorem minors_two_A23 : minors 2 A23 = [-3, -5, -1] := by
  unfold minors
  rw [selectedColumnTuples_two_two, selectedColumnTuples_two_three]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil,
    det_two_by_two, A23]
  decide

/-- The rank over `ℚ` is `2`: the `3 × 3` minors form the empty list, and some
`2 × 2` minor is nonzero. -/
example : ((matrixEquiv A23).map (Int.castRingHom ℚ)).rank = 2 := by
  apply le_antisymm
  · rw [rank_le_iff_minors_succ_map_eq_zero,
      (minors_eq_nil_iff A23 (2 + 1)).mpr (Or.inl (by omega))]
    simp
  · rw [le_rank_iff_exists_minor_map_ne_zero, minors_two_A23]
    exact ⟨-3, by simp, by norm_num⟩

/-- The `2 × 2` Vandermonde matrix `[[1, x_0], [1, x_1]]` over `ℚ`. -/
def V2 : Hex.Matrix (Hex.MvPoly 2 ℚ Hex.Mono.grlex) 2 2 :=
  Hex.Matrix.ofFn fun i j => if j.val = 0 then 1 else Hex.MvPoly.X i

/-- The single `2 × 2` minor of `V2` is `x_1 - x_0`. -/
theorem minors_two_V2 : minors 2 V2 = [Hex.MvPoly.X 1 - Hex.MvPoly.X 0] := by
  unfold minors
  rw [selectedColumnTuples_two_two]
  simp only [List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.append_nil]
  have h2 : ∀ M : Hex.Matrix (Hex.MvPoly 2 ℚ Hex.Mono.grlex) 2 2,
      det M = M[(0 : Fin 2)][(0 : Fin 2)] * M[(1 : Fin 2)][(1 : Fin 2)] -
        M[(1 : Fin 2)][(0 : Fin 2)] * M[(0 : Fin 2)][(1 : Fin 2)] := fun M => det_two_by_two M
  rw [h2]
  simp only [getElem_selectedSubmatrix, V2, getElem_ofFn]
  simp

/-- On the diagonal the rank drops below `2`. -/
example : rankAt V2 ![1, 1] < 2 := by
  rw [rankAt_lt_iff_inLocus, inLocus_iff, minors_two_V2]
  simp [← HexMvPolyMathlib.aeval_eq_eval]

/-- Off the diagonal the rank is `2`. -/
example : ¬ rankAt V2 ![1, 2] < 2 := by
  rw [rankAt_lt_iff_inLocus, inLocus_iff, minors_two_V2]
  simp [← HexMvPolyMathlib.aeval_eq_eval]
  norm_num

/-- The unimodular matrix `[[1, 1], [0, 1]]`. -/
def P22 : Hex.Matrix Int 2 2 :=
  Hex.Matrix.ofFn fun i j => if i.val ≤ j.val then 1 else 0

/-- Its inverse `[[1, -1], [0, 1]]`. -/
def Pinv22 : Hex.Matrix Int 2 2 :=
  Hex.Matrix.ofFn fun i j => if i = j then 1 else if i.val < j.val then -1 else 0

/-- The inverse hypothesis, checked entrywise through `matrixEquiv`. -/
theorem Pinv22_mul_P22 : Pinv22 * P22 = Hex.Matrix.identity 2 := by
  apply matrixEquiv.injective
  rw [matrixEquiv_mul]
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  simp only [matrixEquiv_apply, P22, Pinv22, getElem_ofFn, getElem_identity]
  fin_cases i <;> fin_cases j <;> simp

/-- A row operation by a unimodular matrix preserves the determinantal
ideal. -/
example : Ideal.span {x | x ∈ minors 1 (P22 * A23)} = Ideal.span {x | x ∈ minors 1 A23} :=
  span_minors_mul_left_eq P22 Pinv22 Pinv22_mul_P22 A23 1

end HexDeterminantalIdealMathlib.Tests
