/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly.Lcm

public section

/-!
Additional lemmas for canonical monic associates of dense polynomials.

The normalization operation itself is owned by `HexPoly.Lcm`; this module
collects the general field lemmas needed by polynomial Smith reduction.
-/

namespace Hex.DensePoly

universe u

variable {F : Type u} [Lean.Grind.Field F] [DecidableEq F]

/-- Scaling a polynomial by a nonzero field element preserves its stored size. -/
theorem size_scale_field {a : F} (ha : a ≠ 0) (p : DensePoly F) :
    (scale a p).size = p.size := by
  have hle : (scale a p).size ≤ p.size := by
    rw [scale_eq_scaleImpl]
    exact size_scaleImpl_le a p
  by_cases hp : p.size = 0
  · omega
  have hpPos : 0 < p.size := Nat.pos_of_ne_zero hp
  have hcoeff : (scale a p).coeff (p.size - 1) ≠ (0 : F) := by
    rw [coeff_scale_semiring]
    intro hzero
    rcases Lean.Grind.Field.of_mul_eq_zero hzero with h | h
    · exact ha h
    · exact (coeff_last_ne_zero_of_pos_size p hpPos) h
  apply Nat.le_antisymm hle
  apply Nat.le_of_not_gt
  intro hlt
  exact hcoeff (coeff_eq_zero_of_size_le (scale a p) (by omega))

/-- Compatibility name for the monicity theorem used by Smith clients. -/
theorem monic_monicize {p : DensePoly F} (hp : p ≠ 0) : (monicize p).Monic :=
  monicize_monic hp

/-- The nonzero branch of monic normalization, exposed for algebraic clients. -/
theorem scale_inv_eq_monicize {p : DensePoly F} (hp : p ≠ 0) :
    scale p.leadingCoeff⁻¹ p = monicize p := by
  have hpPos : 0 < p.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    exact hp ((size_eq_zero_iff p).mp hsize)
  have hisZero : p.isZero = false := (isZero_eq_false_iff p).2 hpPos
  rw [monicize, ite_eq_right (by simp [hisZero])]

/-- Every polynomial divides its monic associate. -/
theorem dvd_monicize (p : DensePoly F) : p ∣ monicize p := by
  by_cases hp : p = 0
  · subst p
    rw [monicize_zero]
    exact dvd_zero_poly 0
  have hisZero : p.isZero = false := by
    rw [← Bool.not_eq_true]
    intro h
    exact hp ((size_eq_zero_iff p).mp ((isZero_eq_true_iff p).mp h))
  refine ⟨scale p.leadingCoeff⁻¹ (1 : DensePoly F), ?_⟩
  rw [monicize, ite_eq_right (by simp [hisZero]), ← mul_scale,
    mul_one_right_poly]

/-- A size-one polynomial is the constant polynomial of its leading
coefficient. -/
theorem eq_C_leadingCoeff_of_size_one {p : DensePoly F} (hp : p.size = 1) :
    p = C p.leadingCoeff := by
  have hpPos : 0 < p.size := by omega
  apply ext_coeff
  intro n
  by_cases hn : n = 0
  · subst n
    rw [coeff_C]
    simp only [ite_true]
    rw [leadingCoeff_eq_coeff_last p hpPos]
    have hidx : p.size - 1 = 0 := by omega
    rw [hidx]
  · rw [coeff_C]
    simp only [hn, ite_false]
    exact coeff_eq_zero_of_size_le p (by omega)

end Hex.DensePoly
