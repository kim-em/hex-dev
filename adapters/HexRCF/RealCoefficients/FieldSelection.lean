/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SourceSelection
public import HexRCF.RealCoefficients.NumberField
public import HexRealClosureTheory.Canonical
public section

/-! Assemble source selection from an actual selected generator and existing
`QAdjoin` coordinates. The generator occupies coordinate zero; original
coefficients retain their order after it. No new field representation, native
root search or assumed tuple identity is used by the selection builder. -/
namespace Hex.RCF.RealCoefficients.FieldSelection
open Hex Hex.RealClosure Hex.RealFormula

/-- Append the existing reduced coordinate polynomials at their common
selected generator. The earlier-generator index is always zero. -/
@[expose] def ofPolynomials {version : Nat} (root : Root version) :
    (n : Nat) → (Fin n → DensePoly Rat) → SourceSelection (n+1)
  | 0, _ => .root .nil root
  | n+1, polynomials =>
      .coordinate (ofPolynomials root n (polynomials ∘ Fin.castSucc)) 0
        (polynomials (Fin.last n))

/-- Every coordinate is authenticated by the selected generator and its
actual polynomial; this preparation introduces no inherited identity hole. -/
theorem inherited_false {version : Nat} (root : Root version)
    (polynomials : Fin n → DensePoly Rat) (i : Fin (n+1)) :
    (ofPolynomials root n polynomials).isInherited i = false := by
  induction n with
  | zero => exact Fin.lastCases rfl (fun j => Fin.elim0 j) i
  | succ n ih =>
      exact Fin.lastCases (by simp [ofPolynomials, SourceSelection.isInherited]) (fun j => by
        simpa [ofPolynomials, SourceSelection.isInherited] using
          ih (polynomials ∘ Fin.castSucc) j) i

@[expose] noncomputable def valuation {version : Nat} (root : Root version)
    (polynomials : Fin n → DensePoly Rat) : Fin (n+1) → ℝ :=
  Fin.cases root.real (fun i => (realPoly (polynomials i)).eval root.real)

/-- The generated shared formula authenticates the whole coordinate tuple. -/
theorem formula_valuation {version : Nat} (root : Root version)
    (polynomials : Fin n → DensePoly Rat) :
    (ofPolynomials root n polynomials).formula.toProp (valuation root polynomials) := by
  induction n with
  | zero =>
      refine ⟨trivial, (NativeSelection.identity root _ _).mpr ?_⟩
      rfl
  | succ n ih =>
      refine ⟨?_, (NativeSelection.relation_correct _ _ _ _).mpr ?_⟩
      · apply ((ofPolynomials root n (polynomials ∘ Fin.castSucc)).formula.rename_correct
          Fin.castSucc _).mpr
        have same : valuation root polynomials ∘ Fin.castSucc =
            valuation root (polynomials ∘ Fin.castSucc) := by
          funext i
          refine Fin.cases rfl (fun j => rfl) i
        rw [same]
        exact ih _
      · change valuation root polynomials (Fin.last n).succ =
          (realPoly (polynomials (Fin.last n))).eval (valuation root polynomials 0)
        rfl

/-- The actual fixed-field coordinates supply the selector's polynomial data. -/
@[expose] def prepare {version : Nat} (root : Root version)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) : SourceSelection (n+1) :=
  ofPolynomials root n (fun i => (values i).coeffs)

/-- Exact original coefficient constructions, including their chosen embedding. -/
@[expose] noncomputable def source {version : Nat} (root : Root version)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) : Fin (n+1) → ℝ :=
  Fin.cases root.toCanonical.toReal (fun i => (Coefficients.ofField root.toCanonical (values i)).toReal)

private theorem coordinate_value {version : Nat} (root : Root version)
    (value : QAdjoin root.toCanonical.toAlgebraic) :
    (Coefficients.ofField root.toCanonical value).toReal = (realPoly value.coeffs).eval root.real := by
  rw [Coefficients.ofField_toReal, Root.toCanonical_real]
  have polynomial : realPoly value.coeffs =
      (HexPolyTheory.toPolynomial value.coeffs).map (Rat.castHom ℝ) := by
    ext i
    simp [realPoly, ratCast]
  rw [polynomial, Polynomial.eval_map]

/-- Source authentication follows from the actual existing conversion laws,
without a caller proof about the shape of a nested conjunction. -/
theorem authenticated {version : Nat} (root : Root version)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) :
    (prepare root values).formula.toProp (source root values) := by
  have same : source root values = valuation root (fun i => (values i).coeffs) := by
    funext i
    refine Fin.cases (Root.toCanonical_real root) (fun j => coordinate_value root (values j)) i
  rw [same]
  exact formula_valuation root _

/-- Produce the tuple at the owner's actual original-field presentation. -/
@[expose] def nativeValues {version : Nat} (root : Root version)
    {registry : BaseContext.Registry}
    (presentation : Hex.RealClosure.NumberField.Presentation root.toCanonical registry)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) : Fin (n+1) → presentation.context.Value :=
  Fin.cases presentation.root.convertedValue (fun i => presentation.pack (values i))

/-- The native tuple and original source expressions have exactly the same
selected interpretation. Both generator and coordinate identities come from
the actual presentation factory's companion laws. -/
theorem nativeValues_real {version : Nat} (root : Root version)
    {registry : BaseContext.Registry}
    (presentation : Hex.RealClosure.NumberField.Presentation root.toCanonical registry)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) :
    presentation.model.value ∘ nativeValues root presentation values = source root values := by
  funext i
  refine Fin.cases presentation.generator_value (fun j => ?_) i
  exact (presentation.pack_value (values j)).trans
    (NumberField.value_eq_ofField root.toCanonical (values j))

/-- The generated source selector is satisfied at the actual produced native
tuple. This is mathematical authentication, not a compiled replay verdict. -/
theorem native_authenticated {version : Nat} (root : Root version)
    {registry : BaseContext.Registry}
    (presentation : Hex.RealClosure.NumberField.Presentation root.toCanonical registry)
    (values : Fin n → QAdjoin root.toCanonical.toAlgebraic) :
    (prepare root values).formula.toProp
      (presentation.model.value ∘ nativeValues root presentation values) := by
  rw [nativeValues_real]
  exact authenticated root values

/-- Add the generator coordinate while retaining every original source atom,
including domain guards, and leaving the quantified variable last. -/
@[expose] def matrix (formula : RealFormula.QF (n+1)) : RealFormula.QF (n+2) :=
  formula.rename Fin.succ

theorem matrix_correct (formula : RealFormula.QF (n+1)) (generator : ℝ)
    (values : Fin n → ℝ) (x : ℝ) :
    (matrix formula).toProp (RealFormula.append (Fin.cases generator values) x) ↔
      formula.toProp (RealFormula.append values x) := by
  rw [matrix, RealFormula.QF.rename_correct]
  have same : RealFormula.append (Fin.cases generator values) x ∘ Fin.succ =
      RealFormula.append values x := by
    funext i
    by_cases present : i.val < n <;>
      simp [RealFormula.append, Function.comp_def, present]
  rw [same]

end Hex.RCF.RealCoefficients.FieldSelection
