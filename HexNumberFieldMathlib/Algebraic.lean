/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.Embedding
public import HexNumberFieldMathlib.IntegerRoots
public import Mathlib.RingTheory.Localization.Integral
public section

/-! Every canonical algebraic number is algebraic over the rationals. -/
namespace Hex.AlgebraicNumber

/-- The represented complex number is algebraic over `ℚ`. -/
theorem isAlgebraic (a : AlgebraicNumber) : IsAlgebraic ℚ a.toComplex := by
  apply (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp
  refine ⟨HexPolyZMathlib.toPolynomial a.p, ?_, ?_⟩
  · intro h
    have hp := congrArg HexPolyZMathlib.ofPolynomial h
    exact HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep (by simpa using hp)
  · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      show algebraMap ℤ ℂ = Int.castRingHom ℂ from RingHom.ext_int _ _]
    exact AlgebraicRoot.toComplex_isRoot a.toRoot

instance : Algebra.IsAlgebraic ℚ AlgebraicNumber where
  isAlgebraic a :=
    (isAlgebraic_algHom_iff toComplexAlgHom toComplex_injective).mp (isAlgebraic a)

end Hex.AlgebraicNumber
