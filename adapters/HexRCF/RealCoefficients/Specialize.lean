/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealFormulaMathlib.Semantics
public import HexRealAlgebraicMathlib.Laws
public import HexPolyMathlib.GrindTransport
public import HexPolyMathlib.PolynomialEquivalence

public section

/-! Substitute fixed algebraic coefficients into the shared polynomial syntax. -/

namespace Hex.RCF.RealCoefficients.Specialize

open Hex.RealFormula
open scoped HexMvPolyMathlib

attribute [local instance 2500] Semiring.toGrindSemiring

local instance : CommRing (DensePoly RealAlgebraicNumber) := HexPolyMathlib.denseCommRing

/-- Parameters become constant polynomials; the last coordinate remains the variable. -/
@[expose] def coordinate (values : Fin n → RealAlgebraicNumber)
    (i : Fin (n + 1)) : DensePoly RealAlgebraicNumber :=
  if h : i.val < n then DensePoly.C (values ⟨i.val, h⟩)
  else DensePoly.monomial 1 1

/-- Evaluate the shared syntax in the existing dense-polynomial ring.
Normalization combines equal powers and removes semantic leading cancellation. -/
@[expose] def polynomial (values : Fin n → RealAlgebraicNumber)
    (p : RealFormula.Poly (n + 1)) : DensePoly RealAlgebraicNumber :=
  MvPoly.eval₂ (Int.castRingHom (DensePoly RealAlgebraicNumber)) (coordinate values) p

/-- Interpret the resulting polynomial at any real argument, not only algebraic ones. -/
noncomputable def evaluate (x : ℝ) : DensePoly RealAlgebraicNumber →+* ℝ :=
  (Polynomial.eval₂RingHom RealAlgebraicNumber.toRealHom x).comp
    HexPolyMathlib.equiv.toRingHom

theorem evaluate_coordinate (values : Fin n → RealAlgebraicNumber)
    (x : ℝ) (i : Fin (n + 1)) :
    evaluate x (coordinate values i) = append (fun j => (values j).toReal) x i := by
  simp only [coordinate, append]
  split <;> simp [evaluate, HexPolyMathlib.toPolynomial_C,
    HexPolyMathlib.toPolynomial_monomial, RealAlgebraicNumber.toRealHom]

/-- Substitution preserves the original polynomial at every real argument. -/
theorem polynomial_eval (values : Fin n → RealAlgebraicNumber)
    (p : RealFormula.Poly (n + 1)) (x : ℝ) :
    evaluate x (polynomial values p) = p.eval (append (fun j => (values j).toReal) x) := by
  unfold polynomial RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial]
  rw [MvPolynomial.eval₂_comp_left]
  have hc : (evaluate x).comp (Int.castRingHom (DensePoly RealAlgebraicNumber)) =
      Int.castRingHom ℝ := by ext; simp
  rw [hc]
  congr 1
  funext i
  exact evaluate_coordinate values x i

end Hex.RCF.RealCoefficients.Specialize
