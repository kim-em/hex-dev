/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellExecution
public import HexRCF.RealCoefficients.Gather
public import HexRCF.RealCoefficients.NumberField
public section
/-! Complete native packets from independently owned coefficients and original
guards. The owner's gathering maps retain selected values and literal source
order; the shared formula arity is independent of the number of owners.
This composes native gathering and packet production. Source-expression
quotation, frozen histories and strict missing-record replay remain separate. -/
open scoped List
namespace Hex.RCF.RealCoefficients.GatherCells
open Hex Hex.RealClosure Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {owners : List (Context registry)}

/-- An existing native value retains its exact original owner. Coefficients
and guards can repeat owners independently, without changing schema arity. -/
abbrev Source (owners : List (Context registry)) :=
  (i : Fin owners.length) × (owners[i]).Value

/-- Transport the ordered coefficient tuple through the actual gathered maps. -/
@[expose] def values (shared : Shared base owners) (coefficients : Fin n → Source owners) :
    Fin n → shared.input.context.Value :=
  fun i => shared.value (coefficients i).1 (coefficients i).2

/-- Original guard order is independent of coefficient and owner order. -/
@[expose] def guards (shared : Shared base owners) (original : List (Source owners)) :
    List shared.input.context.Value :=
  original.map fun entry => shared.value entry.1 entry.2

/-- Complete native packets after an already checked gathering. Source values
are transported, never reinterpreted as new independent parameters. -/
@[expose] def buildWith (shared : Shared base owners)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) :=
  CellDiscover.run (values shared coefficients) (guards shared original) formula

/-- Original typed zero tests precede gathering and all cell production. -/
@[expose] def domains (original : List (Source owners)) : Bool :=
  original.all fun entry => Decidable.decide (entry.2 ≠ 0)

inductive Error where
  | divisor
  | gathering
  | discovery (cause : CellDiscover.Error)
  deriving Repr

/-- Gather all declared used owners and produce complete packets. The ordered
guards include values absent from the coefficient tuple or normalized matrix. -/
@[expose] def build (base : BaseContext.PackedContext registry)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) :
    Except Error ((shared : Shared base owners) ×
      CellDiscover.Packet (values shared coefficients) (guards shared original) formula) := do
  unless domains original do throw .divisor
  let some shared := Shared.gather? base owners | throw .gathering
  let packet ← buildWith shared coefficients original formula |>.mapError Error.discovery
  return ⟨shared,packet⟩

/-- Transport preserves each original fixed source coordinate. -/
theorem values_real (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : Fin n → Source owners) :
    (fun i => target.value (values shared coefficients i)) =
      (fun i => (models.get (coefficients i).1).1.value (coefficients i).2) := by
  funext i
  exact models.value (coefficients i).1 (coefficients i).2

private theorem readValue {base : BaseContext.PackedContext registry}
    (following : base.Realization) (reference : Model (Context.ofBase base) ℝ)
    {left right : Context registry} (same : left = right) (original : Model right ℝ)
    (checked : right.model? following reference = some original)
    (a : left.Value) (b : right.Value) (binding : HEq a b) :
    ∃ retained : Model left ℝ, left.model? following reference = some retained ∧
      retained.value a = original.value b := by
  cases same
  cases eq_of_heq binding
  exact ⟨original,checked,rfl⟩

/-- A gathered selected-field coordinate has its original authenticated real
value. The canonical reader equation is derived from the actual presentation;
only the literal owner and coordinate identities are supplied. -/
theorem field_value
    (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    {shared : Shared (.pack (BaseContext.rational registry)) owners}
    (model : Shared.Model shared following (Hex.RealClosure.NumberField.rationalModel registry))
    {generator : RealAlgebraicNumber}
    (source : Hex.RealClosure.NumberField.Presentation generator registry)
    (index : Fin owners.length) (owner : owners[index] = source.context)
    (a : (owners[index]).Value) (b : QAdjoin generator.toAlgebraic)
    (binding : HEq a (source.pack b)) :
    model.target.value (shared.value index a) = (Coefficients.ofField generator b).toReal := by
  obtain ⟨original,checked,value⟩ := readValue following
    (Hex.RealClosure.NumberField.rationalModel registry) owner source.model
    (NumberField.model_read following source) a (source.pack b) binding
  rw [model.value_of_model index original
    ((OwnerReader.ordered_read following (Hex.RealClosure.NumberField.rationalModel registry)
      (owners[index])).trans checked),
    value,source.pack_value,NumberField.value_eq_ofField]

/-- Actual owner interpretations reflect zero before and after gathering. -/
theorem guards_nonzero (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (original : List (Source owners)) (nonzero : ∀ entry ∈ original, entry.2 ≠ 0) :
    ∀ d ∈ guards shared original, d ≠ 0 := by
  intro d member zero
  obtain ⟨entry,present,rfl⟩ := List.mem_map.mp member
  apply nonzero entry present
  apply ((models.get entry.1).1.zero_iff entry.2).mp
  rw [← models.value entry.1 entry.2]
  exact (target.zero_iff _).mpr zero

/-- Complete replay of the emitted packets retains both quantified verdicts
at the original source-owner values. No child success premise is supplied. -/
theorem buildWith_complete (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) (nonzero : ∀ entry ∈ original, entry.2 ≠ 0) :
    ∃ packet, buildWith shared coefficients original formula = .ok packet ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ values shared coefficients) formula
          ((guards shared original).map packet.family.collection.input.value)
          packet.radical quantifier packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (models.get (coefficients i).1).1.value (coefficients i).2)) := by
  simpa only [buildWith,values_real shared target models coefficients] using
    CellDiscover.run_complete target (values shared coefficients) (guards shared original) formula
      (guards_nonzero shared target models original nonzero)

/-- Compatible actual origins supply the gathered model and successful packet
producer. No caller chooses an enlarged target or assumes gathering succeeds.
The ordinary base model remains the interpretation domain hypothesis. -/
theorem build_complete (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (compatible : ∀ owner ∈ owners,
      owner.origin.base.signature.constants <+ base.signature.constants ∧
      owner.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) (nonzero : ∀ entry ∈ original, entry.2 ≠ 0) :
    ∃ shared : Shared base owners, ∃ packet,
      build base coefficients original formula = .ok ⟨shared,packet⟩ ∧
      Shared.gather? base owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ values shared coefficients) formula
          ((guards shared original).map packet.family.collection.input.value)
          packet.radical quantifier packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (model.owners.get (coefficients i).1).1.value (coefficients i).2)) := by
  obtain ⟨shared,gathered,⟨model⟩⟩ := Shared.gather?_models following reference owners compatible
  obtain ⟨packet,produced,checked⟩ :=
    buildWith_complete shared model.target model.owners coefficients original formula nonzero
  have valid : domains original = true := by
    apply List.all_eq_true.mpr
    intro entry member
    exact decide_eq_true (nonzero entry member)
  refine ⟨shared,packet,?_,gathered,model,checked⟩
  simp only [build,valid,↓reduceIte,gathered,produced,Except.mapError,
    bind,Except.bind,pure,Except.pure]

/-- Complete emitted replay at independently presented original selected-field
values. Exact owner/coordinate bindings replace any semantic agreement premise. -/
theorem build_fields_complete
    (following : (BaseContext.PackedContext.pack (BaseContext.rational registry)).Realization)
    (compatible : ∀ owner ∈ owners,
      owner.origin.base.signature.constants <+ (BaseContext.rational registry).signature.constants ∧
      owner.origin.base.signature.infinitesimals ≤ (BaseContext.rational registry).signature.infinitesimals)
    (generators : Fin n → RealAlgebraicNumber)
    (sources : (i : Fin n) → Hex.RealClosure.NumberField.Presentation (generators i) registry)
    (coordinates : (i : Fin n) → QAdjoin (generators i).toAlgebraic)
    (coefficients : Fin n → Source owners)
    (owner : ∀ i, owners[(coefficients i).1] = (sources i).context)
    (binding : ∀ i, HEq (coefficients i).2 ((sources i).pack (coordinates i)))
    (original : List (Source owners)) (formula : RealFormula.QF (n+1))
    (nonzero : ∀ entry ∈ original, entry.2 ≠ 0) :
    ∃ shared : Shared (.pack (BaseContext.rational registry)) owners, ∃ packet,
      build (.pack (BaseContext.rational registry)) coefficients original formula = .ok ⟨shared,packet⟩ ∧
      ∀ quantifier, ∃ verdict,
        CompleteReplay.check packet.family.collection.input.context.codec
          (packet.family.collection.input.value ∘ values shared coefficients) formula
          ((guards shared original).map packet.family.collection.input.value)
          packet.radical quantifier packet.rootGraph packet.cells = .ok verdict ∧
        (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
          (fun i => (Coefficients.ofField (generators i) (coordinates i)).toReal)) := by
  obtain ⟨shared,packet,produced,_gathered,model,checked⟩ :=
    build_complete following (Hex.RealClosure.NumberField.rationalModel registry)
      compatible coefficients original formula nonzero
  have agreed : (fun i => (model.owners.get (coefficients i).1).1.value (coefficients i).2) =
      (fun i => (Coefficients.ofField (generators i) (coordinates i)).toReal) := by
    funext i
    rw [← model.value]
    exact field_value following model (sources i) (coefficients i).1 (owner i)
      (coefficients i).2 (coordinates i) (binding i)
  exact ⟨shared,packet,produced,by simpa only [agreed] using checked⟩

/-- A known original zero rejects before any gathering or carrier work. -/
theorem build_zero (base : BaseContext.PackedContext registry)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) (entry : Source owners)
    (member : entry ∈ original) (zero : entry.2 = 0) :
    build base coefficients original formula = .error .divisor := by
  have invalid : domains original = false := by
    cases checked : domains original with
    | false => rfl
    | true =>
      have nonzero := List.all_eq_true.mp checked entry member
      simp only [decide_eq_true_eq] at nonzero
      exact False.elim (nonzero zero)
  simp only [build,invalid,Bool.false_eq_true,↓reduceIte]
  rfl

/-- Successful production establishes nonzero original typed guards, even
when the source matrix has no coefficients or only constant atoms. -/
theorem build_domains (base : BaseContext.PackedContext registry)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1)) (shared : Shared base owners)
    (packet : CellDiscover.Packet (values shared coefficients) (guards shared original) formula)
    (accepted : build base coefficients original formula = .ok ⟨shared,packet⟩) :
    ∀ entry ∈ original, entry.2 ≠ 0 := by
  intro entry member zero
  rw [build_zero base coefficients original formula entry member zero] at accepted
  cases accepted
/-- Accepted production supplies a compatible gathered interpretation and
both verdicts without assuming original guard validity or compatible origins. -/
theorem build_sound (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (coefficients : Fin n → Source owners) (original : List (Source owners))
    (formula : RealFormula.QF (n+1))
    (result : (shared : Shared base owners) ×
      CellDiscover.Packet (values shared coefficients) (guards shared original) formula)
    (accepted : build base coefficients original formula = .ok result) :
    ∃ model : Shared.Model result.1 following reference,
    ∀ quantifier, ∃ verdict,
      CompleteReplay.check result.2.family.collection.input.context.codec
        (result.2.family.collection.input.value ∘ values result.1 coefficients) formula
        ((guards result.1 original).map result.2.family.collection.input.value)
        result.2.radical quantifier result.2.rootGraph result.2.cells = .ok verdict ∧
      (verdict = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (model.owners.get (coefficients i).1).1.value (coefficients i).2)) := by
  have nonzero := build_domains base coefficients original formula result.1 result.2 accepted
  have valid : domains original = true := by
    apply List.all_eq_true.mpr
    intro entry member
    exact decide_eq_true (nonzero entry member)
  have returned := accepted
  simp only [build,valid,↓reduceIte] at returned
  cases gathered : Shared.gather? base owners with
  | none =>
    simp only [gathered] at returned
    cases returned
  | some shared =>
    obtain ⟨shared,packet,produced,_gathered,model,checked⟩ :=
      build_complete following reference (Shared.gather?_compatible base owners shared gathered)
        coefficients original formula nonzero
    have same : result = ⟨shared,packet⟩ := Except.ok.inj (accepted.symm.trans produced)
    cases same
    exact ⟨model,checked⟩

end Hex.RCF.RealCoefficients.GatherCells
