/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.Reify
open Hex Lean Meta Elab Command Term Qq

namespace Hex.RCF.RealCoefficients.MaximalCoefficientsTests

/-- Check the whole ordered source inventory and its original-goal equivalence.
These are pending schemas; retained zero divisors do not become valid inputs. -/
private meta def check (target : Expr) (coefficients divisors : Array Expr)
    (registered : Array Expr := #[]) : MetaM Unit := do
  let .ok source ← Reify.prepare target {} registered
    | throwError "maximal closed coefficient source was not recognized"
  unless source.coefficients.size == coefficients.size &&
      source.divisors.size == divisors.size do
    throwError "maximal coefficient or original divisor inventory changed"
  for (actual, expected) in source.coefficients.zip coefficients do
    unless ← isDefEq actual expected do
      throwError "coefficient is not the entire original closed expression"
  for (actual, expected) in source.divisors.zip divisors do
    unless ← isDefEq actual expected do
      throwError "original divisor order or identity changed"
  let expected ← mkAppM ``Iff
    #[← mkAppM ``RealFormula.Prenex.toProp #[source.formula,source.valuation],target]
  let proof ← Hex.RCF.checkProof `maximalCoefficientSource expected source.proof
  let axioms ← collectAxioms proof.getAppFn.constName!
  unless axioms.all (#[``propext,``Classical.choice,``Quot.sound].contains ·) do
    throwError "maximal source equivalence has an unexpected axiom"

elab "#maximal_coefficient_sources" : command => liftTermElabM do
  check q(∀ x : ℝ, x^2 + (Real.sqrt 2 + Real.sqrt 3) > 0)
    #[q(Real.sqrt 2 + Real.sqrt 3)] #[]
  check q(∀ x : ℝ, (Real.sqrt 2 + Real.sqrt 3) * x +
      (Real.sqrt 2 + Real.sqrt 3) > 0)
    #[q(Real.sqrt 2 + Real.sqrt 3)] #[]
  check q(∀ x : ℝ, (Real.sqrt 2 + Real.sqrt 3) * x + Real.sqrt 2 > 0)
    #[q(Real.sqrt 2 + Real.sqrt 3),q(Real.sqrt 2)] #[]
  check q(∀ x : ℝ, x^2 + 2 * Real.sqrt 2 > 0)
    #[q((2 : ℝ) * Real.sqrt 2)] #[]
  let wrapped : Q(ℝ) := .mdata {} q(Real.sqrt 2)
  let product : Q(ℝ) := q((2 : ℝ) * $wrapped)
  check q(∀ x : ℝ, x^2 + $product > 0) #[product] #[]
  check q(∀ x : ℝ, x^2 + (-Real.sqrt 2) > 0)
    #[q(-Real.sqrt 2)] #[]
  check q(∀ x : ℝ, x^2 + (Real.sqrt 2 + Real.sqrt 3)^2 > 0)
    #[q((Real.sqrt 2 + Real.sqrt 3)^2)] #[]
  check q(∀ x : ℝ, x / (Real.sqrt 2 + Real.sqrt 3) > 0)
    #[q((Real.sqrt 2 + Real.sqrt 3)⁻¹)] #[q(Real.sqrt 2 + Real.sqrt 3)]
  check q(∀ x : ℝ, x + (Real.sqrt 2 + 1) / (Real.sqrt 2 - 1) > 0)
    #[q((Real.sqrt 2 + 1) / (Real.sqrt 2 - 1))] #[q(Real.sqrt 2 - 1)]
  -- Closed and variable-bearing divisions use the same depth-first preorder.
  check q(∀ x : ℝ, x / (1 / (Real.sqrt 2 - 1)) > 0)
    #[q((1 / (Real.sqrt 2 - 1))⁻¹)]
    #[q(1 / (Real.sqrt 2 - 1)),q(Real.sqrt 2 - 1)]
  check q(∀ x : ℝ, x + 2 / (1 / (Real.sqrt 2 - 1)) > 0)
    #[q((2 : ℝ) / (1 / (Real.sqrt 2 - 1)))]
    #[q(1 / (Real.sqrt 2 - 1)),q(Real.sqrt 2 - 1)]
  check q(∀ x : ℝ, x + (1 / (Real.sqrt 2 - 1))⁻¹ > 0)
    #[q((1 / (Real.sqrt 2 - 1))⁻¹)]
    #[q(1 / (Real.sqrt 2 - 1)),q(Real.sqrt 2 - 1)]
  check q(∀ x : ℝ, x^2 + 0 * (1 / (Real.sqrt 2 - Real.sqrt 2)) = x^2)
    #[q((0 : ℝ) * (1 / (Real.sqrt 2 - Real.sqrt 2)))]
    #[q(Real.sqrt 2 - Real.sqrt 2)]
  check q(∀ x : ℝ, x^2 > Real.pi - 4)
    #[q(Real.pi - 4)] #[]
  check q(∀ x : ℝ, x + (Real.sin 2 + 1) > 0)
    #[q(Real.sin 2 + 1)] #[] #[q(Real.sin 2)]
  logInfo "maximal closed arithmetic, ordered shared subjects, original guards and kernel equivalences checked"
  addDecl (.thmDecl {
    name := `Hex.RCF.RealCoefficients.MaximalCoefficientsTests.complete
    levelParams := [], type := Lean.mkConst ``True, value := Lean.mkConst ``True.intro })

#maximal_coefficient_sources

end Hex.RCF.RealCoefficients.MaximalCoefficientsTests
