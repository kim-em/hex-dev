/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellExecution
public import HexRCF.RealCoefficients.NumberField
public section
/-!
Complete native cell packets from original selected number-field coordinates.
The existing owner factory supplies the checked embedding. Original guards
precede presentation construction; finite-codec replay remains separate.
-/
namespace Hex.RCF.RealCoefficients.NumberField
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
variable {generator : RealAlgebraicNumber} {registry : BaseContext.Registry}

/-- Reuse one checked selected-field presentation for native cell construction. -/
@[expose] def cellsWith (source : Hex.RealClosure.NumberField.Presentation generator registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic))
    (formula : RealFormula.QF (n+1)) :=
  CellDiscover.run (source.pack ∘ values) (guards.map source.pack) formula

/-- Retain the actual construction trace and both verdicts at the original
selected real coefficient values. No parent-model premise is supplied. -/
theorem cellsWith_spec
    (source : Hex.RealClosure.NumberField.Presentation generator registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic))
    (formula : RealFormula.QF (n+1)) (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ packet, cellsWith source values guards formula = .ok packet ∧
      let _ : Hashable packet.family.collection.input.context.Value :=
        RowEncode.hashable packet.family.collection.input.context.codec
      let _ : Hashable Signature := RowEncode.hashable Signature.codec
      ∃ candidates : Vector packet.family.collection.input.context.Value
          (packet.family.values.length+1),
        SectorRequest.points packet.family = some candidates ∧
      ∃ dimensions : packet.family.values.length+1 = packet.roots.roots.length+1,
      ∃ data : CellReplay.Evidence packet.roots
          (packet.family.collection.input.value ∘ (source.pack ∘ values)) formula,
        CellBuild.evidence packet.roots (packet.family.collection.input.value ∘ (source.pack ∘ values))
          ((guards.map source.pack).map packet.family.collection.input.value) formula
          (fun cut => candidates[Fin.cast dimensions.symm cut]) = .ok data ∧
        packet.cells = CellBuild.packet data ∧
        ∀ quantifier, ∃ verdict,
        CellReplay.check (packet.family.collection.input.value ∘ (source.pack ∘ values)) formula
          ((guards.map source.pack).map packet.family.collection.input.value)
          packet.radical packet.roots data quantifier = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (Coefficients.ofField generator (values i)).toReal)) := by
  have packed : ∀ d ∈ guards.map source.pack, d ≠ 0 := by
    intro d member zero
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact guarded old present ((source.pack_zero old).mp zero)
  simpa only [cellsWith, Function.comp_apply,
    Hex.RealClosure.NumberField.Presentation.pack_value, value_eq_ofField] using
    CellDiscover.run_success source.model (source.pack ∘ values)
      (guards.map source.pack) formula packed

/-- Preserve guard, presentation and cell-production failures without retry. -/
inductive CellError where
  | divisor
  | presentation
  | discovery (cause : CellDiscover.Error)
  deriving Repr

/-- Preflight original guards, construct the selected-field presentation and
produce the complete packet in its actual native common context. -/
@[expose] def cells (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic)) (formula : RealFormula.QF (n+1)) :
    Except CellError ((source : Hex.RealClosure.NumberField.Presentation generator registry) ×
      CellDiscover.Packet (source.pack ∘ values) (guards.map source.pack) formula) := do
  unless guards.all (fun d => Decidable.decide (d ≠ 0)) do throw .divisor
  let some source := Hex.RealClosure.NumberField.present? generator registry |
    throw .presentation
  let packet ← cellsWith source values guards formula |>.mapError CellError.discovery
  return ⟨source,packet⟩

/-- Every original field with nonzero guards yields an actual factory result
and packet. The returned source retains its exact cell-producer equation. -/
theorem cells_success (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic)) (formula : RealFormula.QF (n+1))
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ source packet, cells generator registry values guards formula = .ok ⟨source,packet⟩ ∧
      Hex.RealClosure.NumberField.present? generator registry = some source ∧
      cellsWith source values guards formula = .ok packet := by
  obtain ⟨source, ready⟩ := Hex.RealClosure.NumberField.present?_success generator registry
  obtain ⟨packet, returned, _⟩ := cellsWith_spec source values guards formula guarded
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    exact decide_eq_true (guarded d member)
  refine ⟨source,packet,?_,ready,returned⟩
  simp only [cells,all,↓reduceIte,ready,returned,Except.mapError,
    bind,Except.bind,pure,Except.pure]

/-- The selected-field coordinates yield independently accepted complete root
and cell packets. Both verdicts retain their original selected real values. -/
theorem cellsWith_complete
    (source : Hex.RealClosure.NumberField.Presentation generator registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic))
    (formula : RealFormula.QF (n+1)) (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ packet, cellsWith source values guards formula = .ok packet ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ (source.pack ∘ values)) formula
          ((guards.map source.pack).map packet.family.collection.input.value)
          packet.radical quantifier
          packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (Coefficients.ofField generator (values i)).toReal)) := by
  have packed : ∀ d ∈ guards.map source.pack, d ≠ 0 := by
    intro d member zero
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    exact guarded old present ((source.pack_zero old).mp zero)
  simpa only [cellsWith, Function.comp_apply,
    Hex.RealClosure.NumberField.Presentation.pack_value, value_eq_ofField] using
    CellDiscover.run_complete source.model (source.pack ∘ values)
      (guards.map source.pack) formula packed

/-- The actual selected-field presentation factory and native cell producer
return complete serialized evidence with both original-coordinate verdicts. -/
theorem cells_complete (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic)) (formula : RealFormula.QF (n+1))
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    ∃ source packet, cells generator registry values guards formula = .ok ⟨source,packet⟩ ∧
      Hex.RealClosure.NumberField.present? generator registry = some source ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ (source.pack ∘ values)) formula
          ((guards.map source.pack).map packet.family.collection.input.value)
          packet.radical quantifier
          packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (Coefficients.ofField generator (values i)).toReal)) := by
  obtain ⟨source, ready⟩ := Hex.RealClosure.NumberField.present?_success generator registry
  obtain ⟨packet, returned, checked⟩ := cellsWith_complete source values guards formula guarded
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    exact decide_eq_true (guarded d member)
  refine ⟨source,packet,?_,ready,checked⟩
  simp only [cells,all,↓reduceIte,ready,returned,Except.mapError,
    bind,Except.bind,pure,Except.pure]

/-- An original zero divisor rejects even before presentation construction. -/
theorem cells_zero (generator : RealAlgebraicNumber) (registry : BaseContext.Registry)
    (values : Fin n → QAdjoin generator.toAlgebraic)
    (guards : List (QAdjoin generator.toAlgebraic)) (formula : RealFormula.QF (n+1))
    (d : QAdjoin generator.toAlgebraic) (member : d ∈ guards) (zero : d = 0) :
    cells generator registry values guards formula = .error .divisor := by
  have invalid : guards.all (fun d => Decidable.decide (d ≠ 0)) = false := by
    apply List.all_eq_false.mpr
    exact ⟨d,member,by simp [zero]⟩
  unfold cells
  rw [invalid]
  rfl

end Hex.RCF.RealCoefficients.NumberField
