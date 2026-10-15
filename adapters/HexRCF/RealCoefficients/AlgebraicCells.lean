/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.GatherCells
public import HexRealClosure.SharedPresentation
public section
/-! Complete native packets from original real algebraic values. Every input
gets the owner's checked selected presentation. Separate index collections retain
coefficient order and every original divisor, including guard-only values.
This derives the rational interpretation and original models; it does not
assemble frozen histories or establish general frontend quotation. -/
open Hex Hex.RealClosure Hex.RealClosure.Tower
open scoped List
namespace Hex.RCF.RealCoefficients.AlgebraicCells
variable {registry : BaseContext.Registry}

@[expose] def presentations (registry : BaseContext.Registry) :
    {n : Nat} → (generators : Fin n → RealAlgebraicNumber) →
      Option ((i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
  | 0, _ => some (fun i => i.elim0)
  | _+1, generators => do
    let head ← Hex.RealClosure.NumberField.present? (generators 0) registry
    let tail ← presentations registry (fun i => generators i.succ)
    pure (Fin.cases head tail)

theorem presentations_success (registry : BaseContext.Registry)
    (generators : Fin n → RealAlgebraicNumber) :
    ∃ sources, presentations registry generators = some sources := by
  induction n with
  | zero => exact ⟨fun i => i.elim0,rfl⟩
  | succ n ih =>
    obtain ⟨head,first⟩ := Hex.RealClosure.NumberField.present?_success (generators 0) registry
    obtain ⟨tail,rest⟩ := ih (fun i => generators i.succ)
    refine ⟨Fin.cases head tail,?_⟩
    simp only [presentations,first,rest]
    rfl

@[expose] def owners {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry) :=
  List.ofFn fun i => (sources i).context

@[expose] def index {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (i : Fin n) : Fin (owners sources).length := ⟨i.val,by simpa [owners] using i.isLt⟩

theorem owner_eq {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (i : Fin n) : (owners sources)[index sources i] = (sources i).context := by
  simp [owners,index]

@[expose] def stored {left right : Context registry} (same : left = right) (value : right.Value) : left.Value :=
  same.symm ▸ value

theorem stored_heq {left right : Context registry} (same : left = right) (value : right.Value) :
    HEq (stored same value) value := by cases same; rfl

@[expose] def entry {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (i : Fin n) : Hex.RCF.RealCoefficients.GatherCells.Source (owners sources) :=
  ⟨index sources i, stored (owner_eq sources i) (sources i).root.convertedValue⟩

theorem original_base {generator : RealAlgebraicNumber}
    (source : Hex.RealClosure.NumberField.Presentation generator registry) :
    source.context.origin.base = .pack (BaseContext.rational registry) := by
  change source.root.conversion.context.origin.base = _
  rw [source.root.conversion_context,source.root.origin_base]
  exact Context.ofBase_origin_base (.pack (BaseContext.rational registry))

private theorem stored_read
    (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {left right : Context registry} (same : left = right) (original : Model right ℝ)
    (checked : right.model? following (Hex.RealClosure.NumberField.rationalModel registry) = some original) :
    left.model? following (Hex.RealClosure.NumberField.rationalModel registry) =
      some (same.symm ▸ original) := by cases same; exact checked

private theorem stored_value {left right : Context registry} (same : left = right)
    (original : Model right ℝ) (value : right.Value) :
    (same.symm ▸ original).value (stored same value) = original.value value := by cases same; rfl

theorem entry_real {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {shared : Shared (.pack (BaseContext.rational registry)) (owners sources)}
    (model : Shared.Model shared following (Hex.RealClosure.NumberField.rationalModel registry))
    (i : Fin n) :
    model.target.value (shared.value (entry sources i).1 (entry sources i).2) =
      (generators i).toReal := by
  let original : Model ((owners sources)[index sources i]) ℝ :=
    (owner_eq sources i).symm ▸ (sources i).model
  have checked := stored_read following (owner_eq sources i) (sources i).model
    (Hex.RCF.RealCoefficients.NumberField.model_read following (sources i))
  have value := model.value_of_model (index sources i) original
    ((OwnerReader.ordered_read following (Hex.RealClosure.NumberField.rationalModel registry)
      ((owners sources)[index sources i])).trans checked)
    (stored (owner_eq sources i) (sources i).root.convertedValue)
  exact value.trans ((stored_value (owner_eq sources i) (sources i).model
    (sources i).root.convertedValue).trans (sources i).generator_value)

private noncomputable def following (registry : BaseContext.Registry) :
    (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization := by
  have same : (BaseContext.RealPrefix.Model.rational registry).context.finish =
      .pack (BaseContext.rational registry) :=
    congrArg BaseContext.RealPrefix.finish (BaseContext.RealPrefix.Model.rational_context registry)
  exact cast (congrArg BaseContext.PackedContext.Realization same)
    (BaseContext.RealPrefix.Model.rational registry).realization

theorem compatible {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry) :
    ∀ owner ∈ owners sources,
      owner.origin.base.signature.constants <+ (BaseContext.rational registry).signature.constants ∧
      owner.origin.base.signature.infinitesimals ≤ (BaseContext.rational registry).signature.infinitesimals := by
  intro owner member
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
  rw [original_base]
  exact ⟨List.Sublist.refl _,Nat.le_refl _⟩

theorem entry_nonzero {generators : Fin n → RealAlgebraicNumber}
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (i : Fin n) (nonzero : generators i ≠ 0) : (entry sources i).2 ≠ 0 := by
  let original : Model ((owners sources)[index sources i]) ℝ :=
    (owner_eq sources i).symm ▸ (sources i).model
  intro zero
  have isZero := (original.zero_iff (entry sources i).2).mpr zero
  change ((owner_eq sources i).symm ▸ (sources i).model).value
    (stored (owner_eq sources i) (sources i).root.convertedValue) = 0 at isZero
  rw [stored_value,(sources i).generator_value] at isZero
  apply nonzero
  apply RealAlgebraicNumber.toReal_injective
  simpa only [RealAlgebraicNumber.zero_toReal] using isZero

open Hex.RCF.RealCoefficients

@[expose] def coefficients {generators : Fin m → RealAlgebraicNumber}
    (sources : (i : Fin m) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (indices : Fin n → Fin m) := fun i => entry sources (indices i)

@[expose] def guards {generators : Fin m → RealAlgebraicNumber}
    (sources : (i : Fin m) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (original : List (Fin m)) := original.map (entry sources)

abbrev Packet {generators : Fin m → RealAlgebraicNumber}
    (sources : (i : Fin m) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (indices : Fin n → Fin m) (original : List (Fin m)) (formula : Hex.RealFormula.QF (n+1)) :=
  (shared : Shared (.pack (BaseContext.rational registry)) (owners sources)) ×
    CellDiscover.Packet (GatherCells.values shared (coefficients sources indices))
      (GatherCells.guards shared (guards sources original)) formula

inductive Error where
  | divisor
  | presentation
  | cells (cause : GatherCells.Error)
  deriving Repr

@[expose] def build (registry : BaseContext.Registry) (generators : Fin m → RealAlgebraicNumber)
    (indices : Fin n → Fin m) (original : List (Fin m)) (formula : Hex.RealFormula.QF (n+1)) :
    Except Error ((sources : (i : Fin m) →
      Hex.RealClosure.NumberField.Presentation (generators i) registry) ×
      Packet sources indices original formula) := do
  unless original.all (fun i => Decidable.decide (generators i ≠ 0)) do throw .divisor
  let some sources := presentations registry generators | throw .presentation
  let packet ← GatherCells.build (.pack (BaseContext.rational registry))
    (coefficients sources indices) (guards sources original) formula |>.mapError Error.cells
  return ⟨sources,packet⟩

theorem buildWith_complete {generators : Fin m → RealAlgebraicNumber}
    (sources : (i : Fin m) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (indices : Fin n → Fin m) (original : List (Fin m)) (formula : Hex.RealFormula.QF (n+1))
    (nonzero : ∀ i ∈ original, generators i ≠ 0) :
    ∃ shared packet, GatherCells.build (.pack (BaseContext.rational registry))
      (coefficients sources indices) (guards sources original) formula = .ok ⟨shared,packet⟩ ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ GatherCells.values shared (coefficients sources indices)) formula
          ((GatherCells.guards shared (guards sources original)).map packet.family.collection.input.value)
          packet.radical quantifier packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (Hex.RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (generators (indices i)).toReal)) := by
  have valid : ∀ d ∈ guards sources original, d.2 ≠ 0 := by
    intro d member
    obtain ⟨i,present,rfl⟩ := List.mem_map.mp member
    exact entry_nonzero sources i (nonzero i present)
  obtain ⟨shared,packet,produced,_gathered,model,checked⟩ :=
    GatherCells.build_complete (following registry) (Hex.RealClosure.NumberField.rationalModel registry)
      (compatible sources) (coefficients sources indices) (guards sources original) formula valid
  have agreed : (fun i => (model.owners.get (coefficients sources indices i).1).1.value
      (coefficients sources indices i).2) = (fun i => (generators (indices i)).toReal) := by
    funext i
    rw [← model.value]
    exact entry_real sources (following registry) model (indices i)
  exact ⟨shared,packet,produced,by simpa only [agreed] using checked⟩

theorem build_complete (registry : BaseContext.Registry) (generators : Fin m → RealAlgebraicNumber)
    (indices : Fin n → Fin m) (original : List (Fin m)) (formula : Hex.RealFormula.QF (n+1))
    (nonzero : ∀ i ∈ original, generators i ≠ 0) :
    ∃ sources shared packet,
      build registry generators indices original formula = .ok ⟨sources,shared,packet⟩ ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ GatherCells.values shared (coefficients sources indices)) formula
          ((GatherCells.guards shared (guards sources original)).map packet.family.collection.input.value)
          packet.radical quantifier packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (Hex.RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (generators (indices i)).toReal)) := by
  obtain ⟨sources,ready⟩ := presentations_success registry generators
  obtain ⟨shared,packet,produced,checked⟩ := buildWith_complete sources indices original formula nonzero
  have valid : original.all (fun i => Decidable.decide (generators i ≠ 0)) = true := by
    apply List.all_eq_true.mpr
    intro i member
    exact decide_eq_true (nonzero i member)
  refine ⟨sources,shared,packet,?_,checked⟩
  simp only [build,valid,↓reduceIte,ready,produced,Except.mapError,
    bind,Except.bind,pure,Except.pure]

theorem build_zero (registry : BaseContext.Registry) (generators : Fin m → RealAlgebraicNumber)
    (indices : Fin n → Fin m) (original : List (Fin m)) (formula : Hex.RealFormula.QF (n+1))
    (i : Fin m) (member : i ∈ original) (zero : generators i = 0) :
    build registry generators indices original formula = .error .divisor := by
  have invalid : original.all (fun i => Decidable.decide (generators i ≠ 0)) = false := by
    cases checked : original.all (fun i => Decidable.decide (generators i ≠ 0)) with
    | false => rfl
    | true =>
      have contradiction := List.all_eq_true.mp checked i member
      simp only [decide_eq_true_eq] at contradiction
      exact False.elim (contradiction zero)
  simp only [build,invalid,Bool.false_eq_true,↓reduceIte]
  rfl

end Hex.RCF.RealCoefficients.AlgebraicCells
