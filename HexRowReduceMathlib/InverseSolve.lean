/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduceMathlib.RankSpanNullspace
public import HexMatrixMathlib.Algebra
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace HexMatrixMathlib

universe u
variable {F : Type u} [Field F] [DecidableEq F] {n m : Nat}

private theorem inverse_products (A B : Hex.Matrix F n n)
    (h : Hex.Matrix.inverse? A = some B) :
    matrixEquiv A * matrixEquiv B = 1 ∧ matrixEquiv B * matrixEquiv A = 1 := by
  obtain ⟨hl, hr⟩ := Hex.Matrix.inverse?_spec A B h
  have hi : matrixEquiv (Hex.Matrix.identity (R := F) n) = 1 := matrixEquiv_one
  exact ⟨by rw [← matrixEquiv_mul, hl, hi], by rw [← matrixEquiv_mul, hr, hi]⟩

/-- Successful field inversion agrees with Mathlib's nonsingular inverse. -/
theorem inverse?_eq_inv (A B : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = some B → matrixEquiv B = (matrixEquiv A)⁻¹ := by
  intro h
  obtain ⟨hl, hr⟩ := inverse_products A B h
  have hu := _root_.Matrix.isUnit_det_of_right_inverse hl
  calc
    matrixEquiv B = matrixEquiv B * 1 := (mul_one _).symm
    _ = matrixEquiv B * (matrixEquiv A * (matrixEquiv A)⁻¹) := by
      rw [_root_.Matrix.mul_nonsing_inv _ hu]
    _ = (matrixEquiv A)⁻¹ := by rw [← mul_assoc, hr, one_mul]

/-- Computational singularity is exactly determinant zero after transport. -/
theorem inverse?_eq_none (A : Hex.Matrix F n n) :
    Hex.Matrix.inverse? A = none ↔ (matrixEquiv A).det = 0 := by
  constructor
  · intro h
    by_contra hd
    have hr : Hex.Matrix.rowReduce_rank A = n := by
      rw [Hex.Matrix.rowReduce_rank, rank_eq (Hex.Matrix.rowReduce_isRowReduced A)]
      simpa using _root_.Matrix.rank_of_det_ne_zero hd
    exact (Hex.Matrix.inverse?_eq_none A).mp h hr
  · intro hd
    cases h : Hex.Matrix.inverse? A with
    | none => rfl
    | some B =>
      exact False.elim ((_root_.Matrix.det_ne_zero_of_right_inverse
        (inverse_products A B h).1) hd)

omit [DecidableEq F] in
private theorem vector_add (x y : Vector F m) :
    vectorEquiv (x + y) = vectorEquiv x + vectorEquiv y := by
  funext i
  exact Vector.getElem_add x y i.val i.isLt

omit [DecidableEq F] in
private theorem vector_zero : vectorEquiv (0 : Vector F m) = 0 := by
  funext i
  exact Vector.getElem_zero i.val i.isLt

/-- A successful answer represents the affine translate of the entire kernel. -/
theorem solve?_spec (A : Hex.Matrix F n m) (b : Vector F n) (s : Hex.Matrix.SolveData A) :
    Hex.Matrix.solve? A b = some s →
      (matrixEquiv A).mulVec (vectorEquiv s.1) = vectorEquiv b ∧
      s.2 = Hex.Matrix.nullspaceBasisMatrix A ∧
      ∀ x : Fin m → F,
        (matrixEquiv A).mulVec x = vectorEquiv b ↔
          x - vectorEquiv s.1 ∈ LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv A)) := by
  intro h
  obtain ⟨hp, hb, _⟩ := Hex.Matrix.solve?_spec A b s h
  have hp' : (matrixEquiv A).mulVec (vectorEquiv s.1) = vectorEquiv b := by
    rw [← vectorEquiv_mulVec, hp]
  refine ⟨hp', hb, fun x => ?_⟩
  simp only [LinearMap.mem_ker, _root_.Matrix.mulVecLin_apply,
    _root_.Matrix.mulVec_sub, hp', sub_eq_zero]

/-- Failure is equivalent to absence of a Mathlib matrix-vector solution. -/
theorem solve?_eq_none (A : Hex.Matrix F n m) (b : Vector F n) :
    Hex.Matrix.solve? A b = none ↔
      ¬ ∃ x : Fin m → F, (matrixEquiv A).mulVec x = vectorEquiv b := by
  rw [Hex.Matrix.solve?_eq_none]
  apply not_congr
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨vectorEquiv x, by rw [← vectorEquiv_mulVec, hx]⟩
  · rintro ⟨x, hx⟩
    refine ⟨vectorEquiv.symm x, vectorEquiv.injective ?_⟩
    simpa only [vectorEquiv_mulVec, Equiv.apply_symm_apply] using hx

/-- The returned basis spans the kernel used in the affine solution theorem. -/
theorem solve?_span (A : Hex.Matrix F n m) (b : Vector F n) (s : Hex.Matrix.SolveData A)
    (h : Hex.Matrix.solve? A b = some s) :
    Submodule.span F (Set.range fun k => vectorEquiv (Hex.Matrix.col s.2 k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv A)) := by
  rw [(Hex.Matrix.solve?_spec A b s h).2.1]
  simp only [Hex.Matrix.nullspaceBasisMatrix_col]
  exact nullspace_span_eq_ker (Hex.Matrix.rowReduce_isRowReduced A)

/-- Every solution has unique coordinates in the returned affine basis. -/
theorem solve?_parameters (A : Hex.Matrix F n m) (b : Vector F n)
    (s : Hex.Matrix.SolveData A) (h : Hex.Matrix.solve? A b = some s) (x : Fin m → F) :
    (matrixEquiv A).mulVec x = vectorEquiv b ↔
      ∃! c : Fin (m - Hex.Matrix.rowReduce_rank A) → F,
        x = vectorEquiv s.1 + (matrixEquiv s.2).mulVec c := by
  have hx : (matrixEquiv A).mulVec x = vectorEquiv b ↔
      A * vectorEquiv.symm x = b := by
    rw [← vectorEquiv.injective.eq_iff, vectorEquiv_mulVec, Equiv.apply_symm_apply]
  rw [hx, (Hex.Matrix.solve?_spec A b s h).2.2]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨vectorEquiv c, ?_, ?_⟩
    · have he := congrArg vectorEquiv hc
      simpa only [Equiv.apply_symm_apply, vector_add, vectorEquiv_mulVec] using he
    · intro d hd
      apply (vectorEquiv : Vector F (m - Hex.Matrix.rowReduce_rank A) ≃ _).symm.injective
      apply Hex.Matrix.solve?_unique A b s _ _ h
      apply vectorEquiv.injective
      simp only [vectorEquiv_mulVec, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
      have he := congrArg vectorEquiv hc
      simp only [Equiv.apply_symm_apply, vector_add, vectorEquiv_mulVec] at he
      exact add_left_cancel (hd.symm.trans he)
  · rintro ⟨c, hc, _⟩
    refine ⟨vectorEquiv.symm c, vectorEquiv.injective ?_⟩
    simpa only [Equiv.apply_symm_apply, vector_add, vectorEquiv_mulVec] using hc

omit [DecidableEq F] in
private theorem vector_vecMul (y : Vector F n) (A : Hex.Matrix F n m) :
    vectorEquiv (Hex.Matrix.vecMul y A) =
      _root_.Matrix.vecMul (vectorEquiv y) (matrixEquiv A) := by
  rw [vectorEquiv_vecMul]
  funext j
  simp only [Fintype.linearCombination_apply, _root_.Matrix.vecMul, dotProduct,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, vectorEquiv_apply,
    _root_.Matrix.row_apply, matrixEquiv_apply]

/-- The actual returned transform row separates the RHS from the column space. -/
theorem solve_error (A : Hex.Matrix F n m) (b y : Vector F n)
    (h : Hex.Matrix.solve A b = .error y) :
    _root_.Matrix.vecMul (vectorEquiv y) (matrixEquiv A) = 0 ∧
      dotProduct (vectorEquiv y) (vectorEquiv b) ≠ 0 := by
  obtain ⟨ha, hb⟩ := Hex.Matrix.solve_error A b y h
  constructor
  · rw [← vector_vecMul, ha, vector_zero]
  · simpa only [dotProduct_eq] using hb

/-- Inconsistency is equivalent to existence of a left-kernel separator. -/
theorem solve?_none_witness (A : Hex.Matrix F n m) (b : Vector F n) :
    Hex.Matrix.solve? A b = none ↔
      ∃ y : Fin n → F, _root_.Matrix.vecMul y (matrixEquiv A) = 0 ∧
        dotProduct y (vectorEquiv b) ≠ 0 := by
  rw [Hex.Matrix.solve?_none_witness]
  constructor
  · rintro ⟨y, ha, hb⟩
    refine ⟨vectorEquiv y, ?_, ?_⟩
    · rw [← vector_vecMul, ha, vector_zero]
    · simpa only [dotProduct_eq] using hb
  · rintro ⟨y, ha, hb⟩
    refine ⟨vectorEquiv.symm y, vectorEquiv.injective ?_, ?_⟩
    · simpa only [vector_vecMul, vector_zero, Equiv.apply_symm_apply] using ha
    · simpa only [dotProduct_eq, Equiv.apply_symm_apply] using hb

end HexMatrixMathlib
