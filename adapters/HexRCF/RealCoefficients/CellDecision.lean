/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellAlignment
public import HexRCF.RealCoefficients.CellProgress
public section
namespace Hex.RCF.RealCoefficients.CellDecision
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
variable {registry : BaseContext.Registry} {parent : Tower.Context registry}
variable {p : DensePoly parent.Value} {roots : RootReplay.Result p .negInf .posInf}
variable {values : Fin n → parent.Value} {formula : QF (n+1)}

/-- Authentic rows make the strict fold total for both quantifiers, including false. -/
theorem run_total (model : Model parent ℝ) (data : CellReplay.Evidence roots values formula)
    (quantifier : Quantifier) : ∃ verdict, data.run quantifier = some verdict := by
  have rows (cell : Cell roots.roots.length) :
      ∃ verdict, Samples.Row.eval formula (data.row cell) = some verdict :=
    Samples.Row.eval_total formula _ _ (data.exactRow model cell)
  cases quantifier with
  | forallReal =>
    obtain ⟨verdict, evaluated, _⟩ := OptionFold.allArray_spec
      (xs := Cell.all roots.roots.length) (fun cell _ => rows cell)
    exact ⟨verdict, evaluated⟩
  | existsReal =>
    obtain ⟨verdict, evaluated, _⟩ := OptionFold.anyArray_spec
      (xs := Cell.all roots.roots.length) (fun cell _ => rows cell)
    exact ⟨verdict, evaluated⟩

theorem check_total (model : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : CellReplay.Evidence roots values formula) (quantifier : Quantifier)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (checked : cert.check parent.signature
      (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true) :
    ∃ verdict, CellReplay.check values formula guards cert roots data quantifier = .ok verdict := by
  have all : guards.all (fun d => Decidable.decide (d ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro d member
    simpa only [decide_eq_true_eq] using guarded d member
  obtain ⟨verdict, evaluated⟩ := run_total model data quantifier
  exact ⟨verdict, by simp only [CellReplay.check, all, checked, ↓reduceIte, evaluated]⟩

/-- Checked carrier and original guards give exact shared-sentence semantics. -/
theorem check_spec (model : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : QF (n+1)) (guards : List parent.Value)
    (cert : RadicalCert parent.Value Signature)
    (roots : RootReplay.Result cert.core .negInf .posInf)
    (data : CellReplay.Evidence roots values formula) (quantifier : Quantifier)
    (guarded : ∀ d ∈ guards, d ≠ 0)
    (checked : cert.check parent.signature
      (RepresentationCarrier.product (RepresentationSpecialize.prepare values formula)) = true) :
    ∃ verdict, CellReplay.check values formula guards cert roots data quantifier = .ok verdict ∧
      (verdict = true ↔ (Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => model.value (values i))) := by
  obtain ⟨verdict, accepted⟩ := check_total model values formula guards cert roots data quantifier guarded checked
  have evaluated := (CellReplay.check_parts values formula guards cert roots data quantifier verdict accepted).2.2
  refine ⟨verdict, accepted, ?_⟩
  have semantics : data.run quantifier = some true ↔
      (Prenex.quant quantifier (.matrix formula)).toProp (fun i => model.value (values i)) := by
    cases quantifier with
    | forallReal =>
      exact RepresentationCells.forall_rows values formula cert checked roots model
        (data.sample model) (data.inside model) data.row (data.exactRow model)
    | existsReal =>
      exact RepresentationCells.exists_rows values formula cert checked roots model
        (data.sample model) (data.inside model) data.row (data.exactRow model)
  simpa only [evaluated, Option.some.injEq] using semantics


/-- Mathematical existence of accepted typed cells in the actual common context.
The parent model and original guards are the explicit domain hypotheses. Root
coverage, order and ordinary sector points are derived from actual owner laws.
This does not assert serialization or general frontend execution progress. -/
theorem complete (original : Model parent ℝ) (values : Fin n → parent.Value)
    (formula : QF (n+1)) (guards : List parent.Value)
    (guarded : ∀ d ∈ guards, d ≠ 0) :
    let family := Tower.Sample.partition parent (RepresentationSpecialize.prepare values formula)
    let input := family.collection.input
    ∃ packet : Σ cert : RadicalCert input.context.Value Signature,
        @RootReplay.Result registry input.context cert.core .negInf .posInf,
      CellBuild.prepare (input.value ∘ values) (guards.map input.value) formula = .ok packet ∧
      ∃ data : CellReplay.Evidence packet.2 (input.value ∘ values) formula,
        ∀ quantifier, ∃ verdict,
          CellReplay.check (input.value ∘ values) formula (guards.map input.value)
            packet.1 packet.2 data quantifier = .ok verdict ∧
          (verdict = true ↔ (Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => original.value (values i))) := by
  classical
  let family := Tower.Sample.partition parent (RepresentationSpecialize.prepare values formula)
  let input := family.collection.input
  obtain ⟨model⟩ := family.model original
  have domains : ∀ d ∈ guards.map input.value, d ≠ 0 := by
    intro d member zero
    obtain ⟨old, present, rfl⟩ := List.mem_map.mp member
    apply guarded old present
    apply (original.zero_iff old).mp
    rw [← model.input.value old]
    exact (model.input.target.zero_iff _).mpr zero
  obtain ⟨packet, produced, checked⟩ := CellBuild.prepare_success model.input.target
    (input.value ∘ values) (guards.map input.value) formula domains
  have aligned := CellAlignment.aligned values formula family original model packet.1 packet.2 checked
  obtain ⟨points, inside⟩ := CellAlignment.sector_points family original model packet.2 aligned
  let _ : Hashable input.context.Value := ⟨fun a => hash (input.context.codec.encode a).writeBytes⟩
  let _ : Hashable Signature := ⟨fun a => hash (Signature.codec.encode a).writeBytes⟩
  obtain ⟨data⟩ := CellProgress.evidence model.input.target packet.2
    (input.value ∘ values) formula points inside
  refine ⟨packet, produced, data, ?_⟩
  intro quantifier
  obtain ⟨verdict, accepted, meaning⟩ := CellDecision.check_spec model.input.target
    (input.value ∘ values) formula (guards.map input.value) packet.1 packet.2 data quantifier domains checked
  refine ⟨verdict, accepted, ?_⟩
  have same : (fun i => model.input.target.value ((input.value ∘ values) i)) =
      (fun i => original.value (values i)) := funext (fun i => model.input.value (values i))
  simpa only [same] using meaning

end Hex.RCF.RealCoefficients.CellDecision
