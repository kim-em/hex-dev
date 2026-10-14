/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Canonical
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Meaning
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

theorem polynomial_eq (facts : List (Algebraic.SignFact Data.native)) :
    Inputs.polynomialAt facts = polynomial := by
  unfold Inputs.polynomialAt polynomial
  erw [Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts,
    Algebraic.Element.cachedAdd_eq Data.reduction Data.reduction_eq facts,
    Algebraic.Element.cachedMul_eq Data.reduction Data.reduction_eq facts,
    Algebraic.Element.cachedNeg_eq Data.reduction Data.reduction_eq facts,
    Algebraic.Element.cachedNatCast_eq Data.reduction Data.reduction_eq facts]
  rfl

theorem roots_iff (x : ℝ) : x ∈ Canonical.roots.values original ↔ x ^ 2 = Real.sqrt 2 := by
  have all := (Canonical.roots.coverage original).1 x
  have source := RepresentationSpecialize.polynomial_eval original.value original.zero_iff
    original.one original.add original.mul original.nat original.neg values atom x
  have value : RepresentationSpecialize.evaluate original.value original.zero_iff x
      (Inputs.polynomialAt Canonical.facts) = x ^ 2 - Real.sqrt 2 := by
    rw [polynomial_eq]
    change RepresentationSpecialize.evaluate original.value original.zero_iff x
      (RepresentationSpecialize.polynomial values atom) = _
    rw [source]
    unfold atom RealFormula.Poly.eval
    simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
    simp [HexMvPolyMathlib.toMvPolynomial_sub, HexMvPolyMathlib.toMvPolynomial_pow,
      HexMvPolyMathlib.toMvPolynomial_X, RealFormula.append, coefficient]
  rw [HexRealRootsMathlib.Tarski.mem_rootsIn_iff _ (Canonical.roots.domain original).1] at all
  change (RepresentationSpecialize.evaluate original.value original.zero_iff x
    (Inputs.polynomialAt Canonical.facts) = 0 ∧ _) ↔ _ at all
  simpa only [value, sub_eq_zero, Endpoint.map,
    HexRealRootsMathlib.Tarski.inInterval_univ, and_true] using all.symm

theorem roots_eq (x : ℝ) : x ∈ Canonical.roots.values original ↔
    x = Real.sqrt (Real.sqrt 2) ∨ x = -Real.sqrt (Real.sqrt 2) := by
  rw [roots_iff]
  have square := Real.sq_sqrt (Real.sqrt_nonneg (2 : ℝ))
  constructor
  · intro h
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (h.trans square.symm)
  · rintro (rfl | rfl)
    · exact square
    · simpa only [neg_sq] using square

theorem positive_mem : Real.sqrt (Real.sqrt 2) ∈ Canonical.roots.values original :=
  (roots_eq _).mpr (Or.inl rfl)

theorem negative_mem : -Real.sqrt (Real.sqrt 2) ∈ Canonical.roots.values original :=
  (roots_eq _).mpr (Or.inr rfl)

theorem ordered : (Canonical.roots.values original).Pairwise (· < ·) := Canonical.roots.ordered original
#print axioms roots_eq
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Meaning
