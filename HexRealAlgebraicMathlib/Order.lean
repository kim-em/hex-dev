/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Field
public import Mathlib.Algebra.Order.Ring.InjSurj

public section

/-! The executable order as a Mathlib linear order and ordered field. -/

namespace Hex.RealAlgebraicNumber

-- These witnesses do not depend on Laws: the companion must first construct
-- its structures independently, then prove that proof-only package.
instance (priority := 900) instSemanticBEq : LawfulBEq RealAlgebraicNumber where
  eq_of_beq := (beq_iff _ _).mp
  rfl := (beq_iff _ _).mpr rfl

instance (priority := 900) instSemanticDecidableEq : DecidableEq RealAlgebraicNumber :=
  instDecidableEqOfLawfulBEq

/-- The real interpretation preserves the executable minimum. -/
@[simp] theorem min_toReal (a b : RealAlgebraicNumber) :
    (min a b).toReal = Min.min a.toReal b.toReal := by
  unfold min
  split
  · rename_i h
    exact (min_eq_left ((le_iff a b).mp h)).symm
  · rename_i h
    exact (min_eq_right (le_of_not_ge (fun hab => h ((le_iff a b).mpr hab)))).symm

/-- The real interpretation preserves the executable maximum. -/
@[simp] theorem max_toReal (a b : RealAlgebraicNumber) :
    (max a b).toReal = Max.max a.toReal b.toReal := by
  unfold max
  split
  · rename_i h
    exact (max_eq_left ((le_iff b a).mp h)).symm
  · rename_i h
    exact (max_eq_right (le_of_not_ge (fun hba => h ((le_iff b a).mpr hba)))).symm

/-- The linear-order proof transported from real values, using executable data. -/
@[expose, reducible] noncomputable def linearOrder : LinearOrder RealAlgebraicNumber :=
  toReal_injective.linearOrder toReal
    (fun {_ _} => (le_iff _ _).symm) (fun {_ _} => (lt_iff _ _).symm)
    min_toReal max_toReal (fun _ _ => (compare_eq _ _).symm)

instance instLinearOrder : LinearOrder RealAlgebraicNumber where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl := linearOrder.le_refl
  le_trans := linearOrder.le_trans
  le_antisymm := linearOrder.le_antisymm
  lt_iff_le_not_ge := linearOrder.lt_iff_le_not_ge
  le_total := linearOrder.le_total
  toDecidableLE := instDecidableLE
  toDecidableLT := instDecidableLT
  toDecidableEq := instSemanticDecidableEq
  min := min
  max := max
  compare := compare
  min_def := linearOrder.min_def
  max_def := linearOrder.max_def
  compare_eq_compareOfLessAndEq := linearOrder.compare_eq_compareOfLessAndEq

instance : IsStrictOrderedRing RealAlgebraicNumber :=
  Function.Injective.isStrictOrderedRing toReal zero_toReal one_toReal
    add_toReal mul_toReal (fun {_ _} => (le_iff _ _).symm)
    (fun {_ _} => (lt_iff _ _).symm)

/-- The field embedding into the real numbers. -/
@[expose] noncomputable def toRealHom : RealAlgebraicNumber →+* ℝ where
  toFun := toReal
  map_zero' := zero_toReal
  map_one' := one_toReal
  map_add' := add_toReal
  map_mul' := mul_toReal

/-- The same interpretation as an order embedding. -/
@[expose] noncomputable def toRealOrderEmbedding : RealAlgebraicNumber ↪o ℝ where
  toFun := toReal
  inj' := toReal_injective
  map_rel_iff' := (le_iff _ _).symm

/-- Executable absolute value agrees with Mathlib absolute value. -/
theorem abs_eq (a : RealAlgebraicNumber) : abs a = |a| := by
  unfold abs
  split
  · exact (abs_of_neg ‹a < 0›).symm
  · exact (abs_of_nonneg (le_of_not_gt ‹¬a < 0›)).symm

/-- The real interpretation preserves absolute value. -/
@[simp] theorem abs_toReal (a : RealAlgebraicNumber) : (abs a).toReal = |a.toReal| := by
  unfold abs
  split
  · rename_i h
    rw [neg_toReal, abs_of_neg]
    simpa using h
  · rename_i h
    rw [abs_of_nonneg]
    simpa using h

end Hex.RealAlgebraicNumber
