/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Samples
public import HexRCF.RealCoefficients.Coefficients
public import HexRealClosureTheory.NumberFieldTower
public import HexRealClosureTheory.ContextModel
-- The original-source factory binding unfolds only `Presentation.model`:
-- its chosen target is the public root conversion model. No owner proof or
-- arithmetic/search implementation is copied into this adapter.
import all HexRealClosureTheory.NumberFieldTower

public section

namespace Hex.RCF.RealCoefficients.NumberField
open Hex Hex.RealClosure Hex.RealClosure.Tower

/-- Native interpretation agrees with the existing frontend coefficient conversion. -/
theorem value_eq_ofField (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) :
    RealClosure.NumberField.value generator value = (Coefficients.ofField generator value).toReal := by
  apply Complex.ofReal_injective
  rw [RealClosure.NumberField.value_complex, Coefficients.ofField_value]

variable {registry : BaseContext.Registry}

private theorem readRoot (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    (root : Tower.Root (Hex.RealClosure.NumberField.base registry)) :
    root.context.model? following (Hex.RealClosure.NumberField.rationalModel registry) =
      some (root.model (Hex.RealClosure.NumberField.rationalModel registry)) := by
  cases root with
  | point value => exact Context.model?_base following (Hex.RealClosure.NumberField.rationalModel registry)
  | selected descriptor extension built =>
    cases built
    change ((Hex.RealClosure.NumberField.base registry).adjoin descriptor).context.model?
      following (Hex.RealClosure.NumberField.rationalModel registry) =
        some ((Hex.RealClosure.NumberField.rationalModel registry).adjoin descriptor)
    have initial := Context.model?_base following (Hex.RealClosure.NumberField.rationalModel registry)
    change (Hex.RealClosure.NumberField.base registry).model? following
      (Hex.RealClosure.NumberField.rationalModel registry) = some (Hex.RealClosure.NumberField.rationalModel registry) at initial
    rw [Context.model?_adjoin (Hex.RealClosure.NumberField.base registry)
      following (Hex.RealClosure.NumberField.rationalModel registry) descriptor, initial]
    rfl

private theorem readCast (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {left right : Context registry} (same : left = right)
    (first : Model left ℝ) (second : Model right ℝ) (aligned : HEq first second)
    (checked : right.model? following (Hex.RealClosure.NumberField.rationalModel registry) = some second) :
    left.model? following (Hex.RealClosure.NumberField.rationalModel registry) = some first := by
  cases same
  cases eq_of_heq aligned
  exact checked

private theorem readModel (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {generator : RealAlgebraicNumber}
    (source : Hex.RealClosure.NumberField.Presentation generator registry) :
    source.context.model? following (Hex.RealClosure.NumberField.rationalModel registry) = some source.model := by
  exact readCast following source.root.conversion_context
    (source.root.conversionModel (Hex.RealClosure.NumberField.rationalModel registry)).target
    (source.root.model (Hex.RealClosure.NumberField.rationalModel registry))
    (source.root.conversionModel_target (Hex.RealClosure.NumberField.rationalModel registry))
    (readRoot following source.root)

/-- The actual canonical owner reader returns the selected presentation's
original real model. No separate model-agreement premise is required. -/
theorem model_read
    (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {generator : RealAlgebraicNumber}
    (source : Hex.RealClosure.NumberField.Presentation generator registry) :
    source.context.model? following (Hex.RealClosure.NumberField.rationalModel registry) =
      some source.model := readModel following source

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
