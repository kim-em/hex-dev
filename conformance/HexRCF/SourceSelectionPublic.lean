/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public section

/-! Ordinary public-module consumer of inherited source interpretation,
authentication and the complete finite-reader API. No private imports. -/
namespace Hex.RCF.SourceSelectionPublic
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients

@[expose] def inherited : SourceSelection 1 := .inherited .nil

theorem inherited_real (values : Fin 1 → ℝ) : inherited.real values = values := by
  funext i
  fin_cases i
  rfl

theorem authenticated (values : Fin 1 → ℝ) : inherited.formula.toProp values :=
  (inherited.formula_iff values).mpr (inherited_real values).symm

theorem realize {registry : BaseContext.Registry} (context : Tower.Context registry)
    (following : context.origin.base.Realization) (coefficient sample : context.Value)
    (source : ℝ) (fixed : context.origin.RealValue following coefficient source)
    (matrix : RealFormula.QF 2) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and inherited.formula.lift matrix)
      (NativeSpecialize.row context (fun _ => coefficient) sample
        (.and inherited.formula.lift matrix)) = some true) :
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (domain coefficient ∧ read coefficient = source) ∧ domain sample ∧
      matrix.toProp (RealFormula.append (fun _ => source) (read sample)) ∧
      (∀ a ∈ guards, domain a ∧ read a ≠ 0) := by
  obtain ⟨read,domain,closed,negative,identified,present,sizes,meaning,guarded,origin⟩ :=
    SourceSelection.exists_real context following inherited (fun _ => coefficient)
      (fun _ => source) (authenticated _) (fun _ _ => fixed) sample matrix guards nonzero truth
  exact ⟨read,domain,closed,identified 0,present,meaning,guarded⟩

end Hex.RCF.SourceSelectionPublic
