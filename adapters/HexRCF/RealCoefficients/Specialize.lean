/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.RealCoefficients.FieldSpecialize
public import HexRealFormulaMathlib.Semantics
public import HexRealAlgebraicMathlib.Laws
public import HexPolyMathlib.GrindTransport
public import HexPolyMathlib.PolynomialEquivalence

public section

/-! Substitute fixed algebraic coefficients into the shared polynomial syntax.
This is the canonical-field specialization. General representation carriers
still require an operation-preserving specialization bridge. Kernel replay uses
the evaluation theorem and supplied coefficient identities, rather than
unfolding canonical minimal-polynomial and root-isolation searches. -/

namespace Hex.RCF.RealCoefficients.Specialize

open Hex.RealFormula
open scoped HexMvPolyMathlib

-- Select the same semiring dictionary as the Mathlib evaluation theorem;
-- the native dense-polynomial dictionary otherwise takes precedence.
-- The transport retains the executable operations.
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

/-- Prepare every shared atom in its original traversal order, retaining
repeated, zero, and domain-guard atoms before carrier construction. -/
@[expose] def prepare (values : Fin n → RealAlgebraicNumber)
    (formula : RealFormula.QF (n + 1)) : List (DensePoly RealAlgebraicNumber) :=
  formula.polys.map (polynomial values)

/-- Interpret the resulting polynomial at any real argument, not only algebraic ones. -/
@[expose] noncomputable def evaluate (x : ℝ) : DensePoly RealAlgebraicNumber →+* ℝ :=
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

/-- The interpreted degree is the degree after coefficient specialization,
including cancellation of leading terms and the zero polynomial. -/
theorem degree (values : Fin n → RealAlgebraicNumber)
    (p : RealFormula.Poly (n + 1)) :
    ((HexPolyMathlib.toPolynomial (polynomial values p)).map
      RealAlgebraicNumber.toRealHom).natDegree = (polynomial values p).natDegree :=
  FieldSpecialize.degree RealAlgebraicNumber.toRealHom
    (fun _ => by
      rw [← RealAlgebraicNumber.zero_toReal]
      exact RealAlgebraicNumber.toReal_injective.eq_iff) values p

/-- The leading coefficient is interpreted at the same fixed real embedding. -/
theorem leading (values : Fin n → RealAlgebraicNumber)
    (p : RealFormula.Poly (n + 1)) :
    ((HexPolyMathlib.toPolynomial (polynomial values p)).map
      RealAlgebraicNumber.toRealHom).leadingCoeff =
      (polynomial values p).leadingCoeff.toReal :=
  FieldSpecialize.leading RealAlgebraicNumber.toRealHom
    (fun _ => by
      rw [← RealAlgebraicNumber.zero_toReal]
      exact RealAlgebraicNumber.toReal_injective.eq_iff) values p

/-- Prepared atoms evaluate at the fixed authenticated coefficient valuation. -/
theorem prepare_eval (values : Fin n → RealAlgebraicNumber)
    (formula : RealFormula.QF (n + 1)) (x : ℝ) :
    (prepare values formula).map (evaluate x) =
      formula.polys.map (fun q => q.eval (append (fun j => (values j).toReal) x)) := by
  unfold prepare
  rw [List.map_map]
  apply List.map_congr_left
  intro q _
  exact polynomial_eval values q x

/-- The whole prepared atom list retains semantic degree, including cancellation. -/
theorem prepare_degrees (values : Fin n → RealAlgebraicNumber)
    (formula : RealFormula.QF (n + 1)) :
    (prepare values formula).map (fun q =>
      ((HexPolyMathlib.toPolynomial q).map RealAlgebraicNumber.toRealHom).natDegree) =
      (prepare values formula).map DensePoly.natDegree := by
  unfold prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact degree values q

end Hex.RCF.RealCoefficients.Specialize
