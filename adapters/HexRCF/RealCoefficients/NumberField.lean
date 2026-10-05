/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRealClosureMathlib.NumberFieldTower

public section

namespace Hex.RCF.RealCoefficients.NumberField
open Hex

/-- Construct the actual original selected number-field presentation before
specializing source coordinates and producing shared section/sector rows.
All coordinates belong to this original field. Each call constructs its
presentation; callers reusing a checked presentation can pack once and use
`Samples.run` directly. This is diagnostic production, not frozen replay. -/
@[expose] def run (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) : Option Bool :=
  match RealClosure.NumberField.present? generator registry with
  | none => none
  | some source =>
    Samples.run (parent := source.context) (fun i => source.pack (values i)) formula quantifier

/-- The owner factory supplies the selected real model; original fixed-field
coordinates keep that embedding throughout the complete formula traversal. -/
theorem run_spec (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run generator registry values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => RealClosure.NumberField.value generator (values i))) := by
  obtain ⟨source, returned⟩ := RealClosure.NumberField.present?_success generator registry
  obtain ⟨result, accepted, semantic⟩ := Samples.run_spec source.model
    (fun i => source.pack (values i)) formula quantifier
  refine ⟨result, ?_, ?_⟩
  · simpa only [run, returned] using accepted
  · simpa only [RealClosure.NumberField.Presentation.pack_value] using semantic

/-- Every fixed original number field supplies a completed diagnostic result. -/
theorem run_total (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run generator registry values formula quantifier = some result := by
  obtain ⟨result, accepted, _⟩ := run_spec generator registry values formula quantifier
  exact ⟨result, accepted⟩

/-- Exact truth under the original chosen real embedding. This theorem does
not turn compiled evaluation into quotation or certificate evidence. -/
theorem run_true (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    run generator registry values formula quantifier = some true ↔
      (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => RealClosure.NumberField.value generator (values i)) := by
  obtain ⟨result, accepted, semantic⟩ := run_spec generator registry values formula quantifier
  simpa only [accepted, Option.some.injEq] using semantic

end Hex.RCF.RealCoefficients.NumberField
