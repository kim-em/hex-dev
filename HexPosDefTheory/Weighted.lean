/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Congruence
import Mathlib.Tactic.Ring

public section

/-! Weighted sum-of-squares identities for the positive-vector method. -/

namespace Hex.PosDefTheory

variable {R : Type*} [CommRing R] [StarRing R]
variable {n : Type*} [Fintype n]

/-- The ordered-pair identity avoids division by two and works over integers. -/
theorem sum_differences (w : n → n → R) (hw : ∀ i j, w i j = w j i) (x : n → R) :
    ∑ i, ∑ j, w i j * star (x i - x j) * (x i - x j) =
      2 * (∑ i, ∑ j, w i j * star (x i) * x i) -
      2 * (∑ i, ∑ j, w i j * star (x i) * x j) := by
  have hc : (∑ i, ∑ j, w i j * star (x j) * x j) =
      ∑ i, ∑ j, w i j * star (x i) * x i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  have hd : (∑ i, ∑ j, w i j * star (x j) * x i) =
      ∑ i, ∑ j, w i j * star (x i) * x j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hw j i]
  have he (i j : n) : w i j * star (x i - x j) * (x i - x j) =
      w i j * star (x i) * x i - w i j * star (x i) * x j -
      w i j * star (x j) * x i + w i j * star (x j) * x j := by
    rw [star_sub]
    ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hc, hd]
  ring

open Matrix

omit [StarRing R] in
/-- Coordinate products clear a diagonal transform without division. -/
theorem diagonal_descent [DecidableEq n] (v x : n → R) :
    Matrix.diagonal v *ᵥ (fun i => (∏ j ∈ Finset.univ.erase i, v j) * x i) =
      (∏ i, v i) • x := by
  ext i
  rw [Matrix.mulVec_diagonal]
  simp only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    Finset.mul_prod_erase Finset.univ v (Finset.mem_univ i)]

/-- Reflect a positive diagonal congruence using the product of the vector's
coordinates and the complementary coordinate products. -/
theorem reflect_diagonal [PartialOrder R] [NoZeroDivisors R] [Nontrivial R] [PosMulReflectLT R]
    [DecidableEq n] (B : Matrix n n R) (v : n → R) (hB : B.IsHermitian)
    (hstar : ∀ i, star (v i) = v i) (hv : ∀ i, v i ≠ 0)
    (hD : (Matrix.diagonal v * B * Matrix.diagonal v).PosDef)
    (norm_pos : ∀ c : R, c ≠ 0 → 0 < star c * c) : B.PosDef := by
  classical
  let V := Matrix.diagonal v
  have hV : Vᴴ = V := by simpa [V] using hstar
  let C := ∏ i, v i
  have hC : C ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hv i)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hB fun x hx => ?_
  let y := fun i => (∏ j ∈ Finset.univ.erase i, v j) * x i
  have hVy : V *ᵥ y = C • x := diagonal_descent v x
  have hy : y ≠ 0 := by
    intro hz
    have he : C • x = 0 := by simpa [hz] using hVy.symm
    exact hx ((smul_eq_zero.mp he).resolve_left hC)
  have hp := hD.dotProduct_mulVec_pos hy
  have he : star y ⬝ᵥ ((V * B * V) *ᵥ y) =
      star C * (star x ⬝ᵥ (B *ᵥ x)) * C := by
    calc
      _ = star (V *ᵥ y) ⬝ᵥ (B *ᵥ (V *ᵥ y)) := by
        simp only [star_mulVec, hV, dotProduct_mulVec, vecMul_vecMul,
          mulVec_mulVec, Matrix.mul_assoc]
      _ = _ := by
        rw [hVy]
        simp [star_smul, mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul, mul_comm]
  rw [he] at hp
  exact reflect_conjugate_of_norm norm_pos C _ hC hp

/-- A symmetric real matrix with nonpositive off-diagonal entries is positive
definite after diagonal congruence when it has a strictly positive vector
whose image is strictly positive. -/
theorem weighted_posDef [PartialOrder R] [IsStrictOrderedRing R]
    [NoZeroDivisors R] [PosMulReflectLT R] [DecidableEq n]
    (B : Matrix n n R) (v : n → R) (hB : B.IsHermitian)
    (hsym : ∀ i j, B i j = B j i) (hvstar : ∀ i, star (v i) = v i)
    (hoff : ∀ i j, i ≠ j → B i j ≤ 0)
    (hv : ∀ i, 0 < v i) (hbv : ∀ i, 0 < (B *ᵥ v) i)
    (norm_nonneg : ∀ x : R, 0 ≤ star x * x)
    (norm_pos : ∀ x : R, x ≠ 0 → 0 < star x * x) :
    (Matrix.diagonal v * B * Matrix.diagonal v).PosDef := by
  classical
  let D := Matrix.diagonal v * B * Matrix.diagonal v
  have hV : (Matrix.diagonal v)ᴴ = Matrix.diagonal v := by
    simpa using hvstar
  have hD : D.IsHermitian := by
    simpa only [hV] using Matrix.isHermitian_mul_mul_conjTranspose (Matrix.diagonal v) hB
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hD fun x hx => ?_
  let w := fun i j => v i * B i j * v j
  have hw (i j : n) : w i j = w j i := by dsimp [w]; rw [hsym i j]; ring
  have he : (∑ i, ∑ j, w i j * star (x i) * x i) =
      ∑ i, (v i * (B *ᵥ v) i) * (star (x i) * x i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w]
    ring
  have hq : (∑ i, ∑ j, w i j * star (x i) * x j) = star x ⬝ᵥ (D *ᵥ x) := by
    simp only [dotProduct, Matrix.mulVec, D, Matrix.diagonal_mul, Matrix.mul_diagonal,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    dsimp [w]
    ring
  have hep : 0 < ∑ i, (v i * (B *ᵥ v) i) * (star (x i) * x i) := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by simpa [funext_iff] using hx
    apply Finset.sum_pos' (fun j _ => mul_nonneg (mul_pos (hv j) (hbv j)).le
      (norm_nonneg _))
    exact ⟨i, Finset.mem_univ _, mul_pos (mul_pos (hv i) (hbv i))
      (norm_pos _ hi)⟩
  have hdiff : (∑ i, ∑ j, w i j * star (x i - x j) * (x i - x j)) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    apply Finset.sum_nonpos
    intro j _
    by_cases hij : i = j
    · subst j; simp
    · have hw0 : w i j ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonneg_of_nonpos (hv i).le (hoff i j hij)) (hv j).le
      simpa only [mul_assoc] using
        mul_nonpos_of_nonpos_of_nonneg hw0 (norm_nonneg (x i - x j))
  rw [sum_differences w hw x, he, hq, sub_nonpos] at hdiff
  have hp := lt_of_lt_of_le (mul_pos (show (0 : R) < 2 by exact zero_lt_two) hep) hdiff
  exact lt_of_mul_lt_mul_left (by simpa only [mul_zero] using hp)
    (show (0 : R) ≤ 2 by exact zero_le_two)

end Hex.PosDefTheory
