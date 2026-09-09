/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Order
public import Mathlib.RingTheory.Localization.Integral

public section

/-! The image of the canonical real algebraic numbers is exactly the algebraic reals. -/

namespace Hex.RealAlgebraicNumber

/-- Every represented real value is algebraic over the rationals. -/
theorem isAlgebraic (a : RealAlgebraicNumber) : IsAlgebraic ℚ a.toReal := by
  apply (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mp
  have hc : IsAlgebraic ℤ a.toAlgebraic.toComplex := by
    refine ⟨HexPolyZMathlib.toPolynomial a.toAlgebraic.p, ?_, ?_⟩
    · intro h
      have hp := congrArg HexPolyZMathlib.ofPolynomial h
      have hn := HexRootsMathlib.RefinedIsolation.poly_ne_zero a.toAlgebraic.rep
      exact hn (by simpa using hp)
    · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
        show algebraMap ℤ ℂ = Int.castRingHom ℂ from RingHom.ext_int _ _]
      exact AlgebraicRoot.toComplex_isRoot a.toAlgebraic.toRoot
  apply (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℤ ℝ ℂ)
    (algebraMap ℝ ℂ).injective).mp
  change IsAlgebraic ℤ (a.toReal : ℂ)
  rwa [ofReal_toReal]

/-- Every real number algebraic over the rationals has a canonical real representative. -/
theorem range_toReal (r : ℝ) : r ∈ Set.range toReal ↔ IsAlgebraic ℚ r := by
  constructor
  · rintro ⟨a, rfl⟩
    exact isAlgebraic a
  · intro hr
    obtain ⟨p, hp, hroot⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ ℝ).mpr hr
    let q := HexPolyZMathlib.ofPolynomial p
    have hq : q ≠ 0 := by
      intro h
      have h' := congrArg HexPolyZMathlib.toPolynomial h
      exact hp (by simpa [q] using h')
    have hc : Polynomial.aeval (r : ℂ) p = 0 := by
      change Polynomial.aeval ((IsScalarTower.toAlgHom ℤ ℝ ℂ) r) p = 0
      rw [Polynomial.aeval_algHom, AlgHom.comp_apply, hroot, map_zero]
    have hqroot : (HexRootsMathlib.toPolyℂ q).IsRoot (r : ℂ) := by
      simpa only [Polynomial.IsRoot.def, HexRootsMathlib.toPolyℂ, q,
        HexPolyZMathlib.toPolynomial, HexPolyZMathlib.ofPolynomial,
        HexPolyMathlib.toPolynomial_ofPolynomial, Polynomial.aeval_def,
        Polynomial.eval₂_eq_eval_map,
        show algebraMap ℤ ℂ = Int.castRingHom ℂ from RingHom.ext_int _ _] using hc
    obtain ⟨a, _, ha⟩ := (ZPoly.mem_algebraicRoots_iff q hq (r : ℂ)).mpr hqroot
    have har : a.isReal = true := (AlgebraicNumber.isReal_iff a).mpr (by rw [ha]; rfl)
    refine ⟨ofAlgebraic a har, ?_⟩
    change a.toComplex.re = r
    rw [ha]
    rfl

end Hex.RealAlgebraicNumber
