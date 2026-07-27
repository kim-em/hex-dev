/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.Basic

public section

/-!
# Arithmetic correspondence for tower coordinates

These theorems identify every executable mixed-radix operation with the
corresponding operation in `ℂ`.  They are the proof payload from which the
law-bearing field interface will be assembled without replacing any runtime
operation.
-/

namespace Hex.NumberTower

/-- Executable zero denotes complex zero. -/
theorem map_zero (T : NumberTower) :
    T.toComplex (0 : Elem T) = 0 := by
  rw [zero_eq_ofRat]
  simpa using toComplex_ofRat T 0

/-- Executable one denotes complex one. -/
theorem map_one (T : NumberTower) :
    T.toComplex (1 : Elem T) = 1 := by
  rw [one_eq_ofRat]
  simpa using toComplex_ofRat T 1

/-- Coordinate addition computes complex addition. -/
theorem map_add (T : NumberTower) (a b : Elem T) :
    T.toComplex (a + b) = T.toComplex a + T.toComplex b := by
  rw [LevelSemantics.toComplex_eq_denote T (a + b),
    LevelSemantics.toComplex_eq_denote T a,
    LevelSemantics.toComplex_eq_denote T b, coeffs_add]
  simpa [dim] using
    LevelSemantics.denote_add T.levels.toList (coeffs a) (coeffs b)

/-- Coordinate negation computes complex negation. -/
theorem map_neg (T : NumberTower) (a : Elem T) :
    T.toComplex (-a) = -T.toComplex a := by
  have h := map_add T a (-a)
  rw [NumberTower.add_neg_self, map_zero] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- Coordinate subtraction computes complex subtraction. -/
theorem map_sub (T : NumberTower) (a b : Elem T) :
    T.toComplex (a - b) = T.toComplex a - T.toComplex b := by
  rw [NumberTower.sub_eq_add_neg, map_add, map_neg]
  rfl

/-- Recursive reduced multiplication computes complex multiplication. -/
theorem map_mul (T : NumberTower) (a b : Elem T) :
    T.toComplex (a * b) = T.toComplex a * T.toComplex b := by
  sorry

/-- Recursive extended-gcd inversion computes complex inversion, including
the executable convention `0⁻¹ = 0`. -/
theorem map_inv (T : NumberTower) (a : Elem T) :
    T.toComplex a⁻¹ = (T.toComplex a)⁻¹ := by
  sorry

/-- Tower division computes complex division. -/
theorem map_div (T : NumberTower) (a b : Elem T) :
    T.toComplex (a / b) = T.toComplex a / T.toComplex b := by
  change T.toComplex (a * b⁻¹) = _
  rw [map_mul, map_inv]
  rfl

/-- The executable rational scalar action is semantic scalar multiplication. -/
theorem map_smul (T : NumberTower) (q : Rat) (a : Elem T) :
    T.toComplex (q • a) = (q : ℂ) * T.toComplex a := by
  sorry

/-- The Boolean zero test recognizes exactly semantic zero. -/
theorem isZero_iff (T : NumberTower) (a : Elem T) :
    NumberTower.isZero a ↔ T.toComplex a = 0 := by
  rw [NumberTower.isZero_iff_eq_zero]
  constructor
  · rintro rfl
    exact map_zero T
  · intro h
    apply toComplex_injective T
    rw [h, map_zero]

/-- Mixed-radix coordinate equality is exactly semantic equality. -/
theorem eq_iff_toComplex (T : NumberTower) (a b : Elem T) :
    a = b ↔ T.toComplex a = T.toComplex b := by
  constructor
  · exact fun h => congrArg T.toComplex h
  · intro h
    exact @toComplex_injective T a b h

namespace Extension

/-- An extension embedding preserves the fixed absolute embedding. This is a
property of checked constructors, not of arbitrary `Extension` records. -/
def PreservesEmbedding {T : NumberTower} (E : Extension T) : Prop :=
  ∀ a, E.tower.toComplex (E.embed a) = T.toComplex a

/-- The distinguished generator denotes the extension's stored absolute
root. -/
def GeneratorValue {T : NumberTower} (E : Extension T) : Prop :=
  E.tower.toComplex E.gen = E.root.toComplex

end Extension

end Hex.NumberTower
