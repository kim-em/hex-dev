/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.Coefficients
public import HexRealClosureTheory.NumberFieldTower

public section

namespace Hex.RCF.RealCoefficients.NumberField
open Hex

/-- Native interpretation agrees with the existing frontend coefficient conversion. -/
theorem value_eq_ofField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) :
    RealClosure.NumberField.value generator value = (Coefficients.ofField generator value).toReal := by
  apply Complex.ofReal_injective
  rw [RealClosure.NumberField.value_complex, Coefficients.ofField_value]

/-- Reuse one checked original-field presentation for shared sentence production. -/
@[expose] def runWith {generator : RealAlgebraicNumber}
    {registry : RealClosure.BaseContext.Registry}
    (source : RealClosure.NumberField.Presentation generator registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) : Option Bool :=
  Samples.run (parent := source.context) (fun i => source.pack (values i)) formula quantifier

/-- A reused presentation preserves the original selected coordinate values. -/
theorem runWith_spec {generator : RealAlgebraicNumber}
    {registry : RealClosure.BaseContext.Registry}
    (source : RealClosure.NumberField.Presentation generator registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, runWith source values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => RealClosure.NumberField.value generator (values i))) := by
  obtain ⟨result, accepted, semantic⟩ := Samples.run_spec source.model
    (fun i => source.pack (values i)) formula quantifier
  refine ⟨result, accepted, ?_⟩
  simpa only [RealClosure.NumberField.Presentation.pack_value] using semantic

/-- Construct the actual original selected number-field presentation before
specializing source coordinates and producing shared section/sector rows.
All coordinates belong to this original field. Each call constructs its
presentation; `runWith` reuses a checked presentation. This is diagnostic
production, not frozen replay. -/
@[expose] def run (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) : Option Bool :=
  match RealClosure.NumberField.present? generator registry with
  | none => none
  | some source => runWith source values formula quantifier

/-- The owner factory supplies the selected real model; original fixed-field
coordinates keep that embedding throughout the complete formula traversal. -/
theorem run_spec (generator : RealAlgebraicNumber) (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run generator registry values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => RealClosure.NumberField.value generator (values i))) := by
  obtain ⟨source, returned⟩ := RealClosure.NumberField.present?_success generator registry
  obtain ⟨result, accepted, semantic⟩ := runWith_spec source values formula quantifier
  refine ⟨result, ?_, ?_⟩
  · simpa only [run, returned] using accepted
  · exact semantic

/-- Sentence production has the frontend's existing fixed-field coefficient semantics. -/
theorem run_coefficients (generator : RealAlgebraicNumber)
    (registry : RealClosure.BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, run generator registry values formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (Coefficients.ofField generator (values i)).toReal)) := by
  simpa only [value_eq_ofField] using run_spec generator registry values formula quantifier

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
