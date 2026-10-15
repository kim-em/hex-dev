/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.Adjugate

public section

/-! Congruence reflection by adjugates, including over integer rings. -/

namespace Hex.PosDefTheory

open Matrix

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [NoZeroDivisors R]
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [NoZeroDivisors R] in
/-- Positivity of a diagonal matrix follows directly from squared norms. -/
theorem diagonal_posDef [IsStrictOrderedRing R] (d : n → R)
    (hd : ∀ i, 0 < d i) (hstar : ∀ i, star (d i) = d i)
    (hn : ∀ x : R, 0 ≤ star x * x)
    (hp : ∀ x : R, x ≠ 0 → 0 < star x * x) : (Matrix.diagonal d).PosDef := by
  have hD : (Matrix.diagonal d).IsHermitian := by
    change (Matrix.diagonal d)ᴴ = Matrix.diagonal d
    simpa using hstar
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hD fun x hx => ?_
  have he : star x ⬝ᵥ (Matrix.diagonal d *ᵥ x) = ∑ i, d i * (star (x i) * x i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Matrix.mulVec_diagonal]
    simp only [Pi.star_apply]
    ac_rfl
  rw [he]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by simpa [funext_iff] using hx
  exact Finset.sum_pos' (fun j _ => mul_nonneg (hd j).le (hn _))
    ⟨i, Finset.mem_univ _, mul_pos (hd i) (hp _ hi)⟩

omit [NoZeroDivisors R] in
/-- Scalar reflection only needs positive squared norms. -/
theorem reflect_conjugate_of_norm [PosMulReflectLT R]
    (norm_pos : ∀ c : R, c ≠ 0 → 0 < star c * c)
    (c q : R) (hc : c ≠ 0) (hp : 0 < star c * q * c) : 0 < q := by
  have he : (star c * c) * 0 < (star c * c) * q := by
    simpa only [mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using hp
  exact lt_of_mul_lt_mul_left he (norm_pos c hc).le

/-- Cancel a nonzero scalar conjugation in the compatible star order. -/
theorem reflect_conjugate [Nontrivial R] [StarOrderedRing R] [PosMulReflectLT R]
    (c q : R) (hc : c ≠ 0) (hp : 0 < star c * q * c) : 0 < q := by
  have hn : 0 < star c * c := star_mul_self_pos (IsRegular.of_ne_zero hc)
  have he : (star c * c) * 0 < (star c * c) * q := by
    simpa only [mul_zero, zero_mul, mul_assoc, mul_comm, mul_left_comm] using hp
  exact lt_of_mul_lt_mul_left he hn.le

/-- A nonzero determinant suffices for congruence reflection without division.
The scalar hypothesis is satisfied by ordered domains and by complex numbers. -/
theorem posDef_of_congruence {B T : Matrix n n R}
    (hB : B.IsHermitian) (hT : T.det ≠ 0)
    (h : (T * B * Tᴴ).PosDef)
    (reflect : ∀ (c q : R), c ≠ 0 → 0 < star c * q * c → 0 < q) : B.PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos hB fun x hx => ?_
  let N := Tᴴ
  let y := N.adjugate *ᵥ x
  have hdet : N.det ≠ 0 := by simpa [N, det_conjTranspose] using star_ne_zero.mpr hT
  have hNy : N *ᵥ y = N.det • x := by
    change N *ᵥ (N.adjugate *ᵥ x) = _
    rw [mulVec_mulVec, mul_adjugate]
    simp only [smul_mulVec, one_mulVec]
  have hy : y ≠ 0 := by
    intro hz
    have : N.det • x = 0 := by simpa [hz] using hNy.symm
    exact hx ((smul_eq_zero.mp this).resolve_left hdet)
  have hp := h.dotProduct_mulVec_pos hy
  have he : star y ⬝ᵥ ((T * B * Tᴴ) *ᵥ y) =
      star N.det * (star x ⬝ᵥ (B *ᵥ x)) * N.det := by
    calc
      _ = star (N *ᵥ y) ⬝ᵥ (B *ᵥ (N *ᵥ y)) := by
        simp only [N, star_mulVec, conjTranspose_conjTranspose, dotProduct_mulVec,
          vecMul_vecMul, mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by
        rw [hNy]
        simp [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul,
          mul_comm]
  rw [he] at hp
  exact reflect N.det _ hdet hp

end Hex.PosDefTheory
