/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Specialize
public import HexRealClosureMathlib.BaseContext
public import Mathlib.Analysis.Real.Sqrt

public section

namespace Hex.RealClosure.Specialize.Tests
attribute [local instance 2000] Field.toGrindField

/-- The same ordinary parameter satisfies all fraction signs and denominator
guards together with the square-root equation and strict infinitesimal inequalities. -/
example (fractions : Finset (Hex.RationalFn ℝ)) :
    ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s ^ 2 = t ∧ t < s ∧ s < 1 ∧
      ∀ f ∈ fractions, (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
        (SignType.sign (evalFraction f t) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  obtain ⟨t, positive, small, signs⟩ := exists_fraction_parameter fractions 1 zero_lt_one
  have square : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt positive.le
  have nonnegative : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have root_positive : 0 < Real.sqrt t := Real.sqrt_pos.mpr positive
  refine ⟨t, Real.sqrt t, positive, small, root_positive, square, ?_, ?_, signs⟩
  · nlinarith
  · nlinarith

/-- Zero polynomials retain zero sign in the same finite-family realization. -/
example (polynomials : Finset (Polynomial ℝ)) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ (SignType.sign ((0 : Polynomial ℝ).eval t) : Int) = 0 ∧
      ∀ p ∈ polynomials, SignType.sign (p.eval t) = SignType.sign p.trailingCoeff := by
  obtain ⟨t, ht, hc, signs⟩ := exists_parameter polynomials cap positive
  exact ⟨t, ht, hc, by simp, signs⟩

/-- Rational coefficient data is embedded through its actual cast, and every
sign and denominator guard uses the same parameter as the selected square root. -/
example (fractions : Finset (Hex.RationalFn Rat)) :
    ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s ^ 2 = t ∧ t < s ∧ s < 1 ∧
      ∀ fraction ∈ fractions,
        ((HexPolyMathlib.toPolynomial fraction.den).map (Rat.castHom ℝ)).eval t ≠ 0 ∧
        (SignType.sign (evalMapped (Rat.castHom ℝ) fraction t) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  obtain ⟨t, positive, small, signs⟩ := exists_mapped_parameter
    (Rat.castHom ℝ) Rat.cast_strictMono fractions 1 zero_lt_one
  have square : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt positive.le
  have nonnegative : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have root_positive : 0 < Real.sqrt t := Real.sqrt_pos.mpr positive
  refine ⟨t, Real.sqrt t, positive, small, root_positive, square, ?_, ?_, signs⟩
  · nlinarith
  · nlinarith

/-- All operands, results, signs and arithmetic identities use one ordinary
parameter for actual native addition and multiplication over an embedded field. -/
example {F : Type} [Field F] [DecidableEq F] [LinearOrder F]
    (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (first second : Hex.RationalFn F) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧
      evalMapped embedding (first + second) t =
        evalMapped embedding first t + evalMapped embedding second t ∧
      evalMapped embedding (first * second) t =
        evalMapped embedding first t * evalMapped embedding second t ∧
      ∀ fraction ∈ ({first, second, first + second, first * second} : Finset (Hex.RationalFn F)),
        ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
        (SignType.sign (evalMapped embedding fraction t) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  obtain ⟨t, ht, small, signs⟩ := exists_mapped_parameter embedding ordered
    {first, second, first + second, first * second} cap positive
  refine ⟨t, ht, small, ?_, ?_, signs⟩
  · exact evalMapped_add embedding first second t
      (signs first (by simp)).1 (signs second (by simp)).1 (signs (first + second) (by simp)).1
  · exact evalMapped_mul embedding first second t
      (signs first (by simp)).1 (signs second (by simp)).1 (signs (first * second) (by simp)).1

section Native
local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private theorem transported_sign {F : Type} [Field F] [DecidableEq F]
    (g : Lean.Grind.Field F) (compatible : Field.toGrindField (K := F) = g)
    (sign : F → Int) (fraction : @Hex.RationalFn F g inferInstance) :
    @Hex.OrderedFn.Infinitesimal.sign F Field.toGrindField inferInstance sign
      (@BaseContext.modelFraction F inferInstance g inferInstance compatible fraction) =
      @Hex.OrderedFn.Infinitesimal.sign F g inferInstance sign fraction := by
  cases compatible
  rfl

private def nativeSign (registry : BaseContext.Registry)
    (a : BaseContext.Element (BaseContext.rational registry).infinitesimal) : Int := a.sign

private def storedFraction (registry : BaseContext.Registry)
    (a : BaseContext.Element (BaseContext.rational registry).infinitesimal) :
    @Hex.RationalFn Rat Field.toGrindField inferInstance :=
  BaseContext.modelFraction HexRationalFnMathlib.ratField_eq a.stored

private theorem stored_sign (registry : BaseContext.Registry)
    (a : BaseContext.Element (BaseContext.rational registry).infinitesimal) :
    @Hex.OrderedFn.Infinitesimal.sign Rat Field.toGrindField inferInstance Hex.OrderedFn.orderSign
      (storedFraction registry a) = nativeSign registry a :=
  transported_sign Lean.Grind.instFieldRat HexRationalFnMathlib.ratField_eq Hex.OrderedFn.orderSign a.stored

/-- A value stored by the actual native rational infinitesimal context enters
specialization through the proved equality of the whole coefficient dictionary. -/
example (registry : BaseContext.Registry)
    (a : BaseContext.Element (BaseContext.rational registry).infinitesimal) :
    letI : Lean.Grind.Field Rat := Field.toGrindField
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧
      ((HexPolyMathlib.toPolynomial
        (storedFraction registry a).den).map
          (Rat.castHom ℝ)).eval t ≠ 0 ∧
      (SignType.sign (evalMapped (Rat.castHom ℝ)
        (storedFraction registry a) t) : Int) = nativeSign registry a := by
  let : Lean.Grind.Field Rat := Field.toGrindField
  let fraction := storedFraction registry a
  have correct (x : Rat) : Hex.OrderedFn.orderSign x = (SignType.sign ((Rat.castHom ℝ) x) : Int) := by
    rw [Rat.cast_strictMono.sign_comp, Hex.OrderedFn.Infinitesimal.orderSign_eq]
  obtain ⟨t, positive, small, signs⟩ := exists_parameter_with (Rat.castHom ℝ)
    Rat.cast_strictMono Hex.OrderedFn.orderSign correct {fraction} 1 zero_lt_one
  obtain ⟨guard, sign⟩ := signs fraction (by simp)
  refine ⟨t, positive, small, guard, ?_⟩
  exact sign.trans (stored_sign registry a)

end Native

end Hex.RealClosure.Specialize.Tests
