/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Algebraic
public import Mathlib.Algebra.Polynomial.Degree.SmallDegree

public section

/-! Exact rational recognition from the canonical minimal polynomial. -/

namespace Hex.RealAlgebraicNumber

/-- Rational construction is injective. -/
theorem ofRat_injective : Function.Injective ofRat := by
  intro p q h
  have hr := congrArg toReal h
  simpa only [ofRat_toReal, Rat.cast_inj] using hr

/-- A linear stored polynomial determines the rational value by its two coefficients. -/
theorem eq_of_degree_one (a : RealAlgebraicNumber) (hd : a.toAlgebraic.p.natDegree = 1) :
    a = ofRat (-(a.toAlgebraic.p.coeff 0 : Rat) / (a.toAlgebraic.p.coeff 1 : Rat)) := by
  let p := HexRootsMathlib.toPolyℂ a.toAlgebraic.p
  have hdeg : p.natDegree = 1 := (HexRootsMathlib.natDegree_toPolyℂ _).trans hd
  have hp : p ≠ 0 := by
    intro h
    simp [h] at hdeg
  have hc : p.coeff 1 ≠ 0 := by
    rw [← hdeg, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hp
  have hz : p.eval a.toAlgebraic.toComplex = 0 :=
    AlgebraicRoot.toComplex_isRoot a.toAlgebraic.toRoot
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one (le_of_eq hdeg)] at hz
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X] at hz
  apply ext
  apply AlgebraicNumber.toComplex_injective
  rw [ofRat_toAlgebraic, AlgebraicNumber.ofRat_toComplex]
  push_cast
  rw [← HexRootsMathlib.coeff_toPolyℂ a.toAlgebraic.p 0,
    ← HexRootsMathlib.coeff_toPolyℂ a.toAlgebraic.p 1]
  apply (eq_div_iff hc).mpr
  linear_combination hz

/-- A rational canonical value has a linear stored minimal polynomial. -/
theorem ofRat_degree (q : Rat) : (ofRat q).toAlgebraic.p.natDegree = 1 := by
  rw [ofRat_toAlgebraic]
  let a := AlgebraicNumber.ofRat q
  have hlc : (a.p.leadingCoeff : Rat) ≠ 0 := by exact_mod_cast ne_of_gt a.pos_lc
  have h := congrArg Polynomial.natDegree (AlgebraicNumber.p_eq_minpoly a)
  rw [Polynomial.natDegree_smul _ (inv_ne_zero hlc)] at h
  have hq : a.toComplex = algebraMap Rat ℂ q := AlgebraicNumber.ofRat_toComplex q
  rw [hq, minpoly.eq_X_sub_C, Polynomial.natDegree_X_sub_C] at h
  rw [HexPolyZMathlib.toPolyℚ,
    Polynomial.natDegree_map_eq_of_injective (RingHom.injective_int (Int.castRingHom ℚ)),
    HexPolyMathlib.natDegree_toPolynomial] at h
  exact h

/-- Rational recognition is sound and complete, including at zero. -/
theorem toRat?_eq_some (a : RealAlgebraicNumber) (q : Rat) :
    a.toRat? = some q ↔ a = ofRat q := by
  constructor
  · intro h
    dsimp only [toRat?] at h
    split at h
    · rename_i hd
      have heq := Option.some.inj h
      rw [← heq]
      exact eq_of_degree_one a hd
    · cases h
  · intro h
    subst a
    have hd := ofRat_degree q
    have heq := eq_of_degree_one (ofRat q) hd
    have hq := ofRat_injective heq
    dsimp only [toRat?]
    rw [ite_eq_left hd]
    exact congrArg some hq.symm

end Hex.RealAlgebraicNumber
