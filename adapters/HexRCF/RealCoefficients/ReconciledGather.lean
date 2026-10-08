/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Gather
public import HexRealClosureMathlib.ReconciledCatalog

public section
open scoped List
namespace Hex.RCF.RealCoefficients.Gather
open Hex RealClosure RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {owners : List (Context registry)}

/-- Native gathering with checked provider reconciliation preserves the
original coordinate order. Decline supplies no Boolean result. This does not
authenticate source expressions or replay a frozen certificate. -/
@[expose] def runReconciled? (catalog : BaseContext.Catalog registry)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    Option Bool :=
  match Shared.gatherReconciledFrom? catalog owners with
  | none => none
  | some ⟨_, shared⟩ => Samples.run (values shared coefficients) formula quantifier

/-- A common ordinary-real model interprets every original coordinate at the
same real variable after actual reconciled selection. -/
theorem runReconciled?_spec (catalog : BaseContext.Catalog registry)
    (shared : Shared base owners)
    (gathered : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, runReconciled? catalog coefficients formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (models.get i).1.value (coefficients i))) := by
  obtain ⟨result, produced, semantic⟩ :=
    run_spec shared target models coefficients formula quantifier
  exact ⟨result, by simpa only [runReconciled?, gathered] using produced, semantic⟩

/-- Separately authenticated original models retain their exact values when
they are the reconciled factory results. Key containment alone is insufficient. -/
theorem runReconciled?_original (catalog : BaseContext.Catalog registry)
    (following : base.Realization) (reference : Model (Context.ofBase base) ℝ)
    (shared : Shared base owners)
    (gathered : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩)
    (original : (i : Fin owners.length) → Model (owners[i]) ℝ)
    (sourceModels : ∀ i, (owners[i]).reconciledModel? following reference = some (original i))
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, runReconciled? catalog coefficients formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (original i).value (coefficients i))) := by
  let model := Shared.Model.ofReconciledGather following reference owners shared
    (Shared.gatherReconciledFrom?_gathered catalog owners base shared gathered)
  have aligned : (fun i => model.target.value (values shared coefficients i)) =
      (fun i => (original i).value (coefficients i)) := by
    funext i
    exact model.value_of_model i (original i) (sourceModels i) (coefficients i)
  obtain ⟨result, produced, semantic⟩ :=
    Samples.run_spec model.target (values shared coefficients) formula quantifier
  refine ⟨result, ?_, ?_⟩
  · simpa only [runReconciled?, gathered] using produced
  · simpa only [aligned] using semantic

/-- An installed modeled joint prefix admits distinct contained provider paths
in any order. Depth-zero original bases supply an ordinary-real target model;
symbolic infinitesimals still require a separate finite-joint realization. -/
theorem gather_history (catalog : BaseContext.Catalog registry)
    (interpreted : catalog.Models)
    (candidate : BaseContext.RealPrefix registry) (installed : candidate ∈ catalog.prefixes)
    (compatible : ∀ owner ∈ owners,
      owner.origin.base.signature.constants.Nodup ∧
        owner.origin.base.signature.constants ⊆ candidate.keys ∧ owner.origin.base.depth = 0)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ (selected : BaseContext.PackedContext registry) (shared : Shared selected owners),
      Shared.gatherReconciledFrom? catalog owners = some ⟨selected, shared⟩ ∧
      ∃ provider : BaseContext.RealPrefix.Model registry,
        provider.context ∈ catalog.prefixes ∧ selected = provider.context.finish ∧
        ∃ (following : selected.Realization) (reference : Model (Context.ofBase selected) ℝ),
          HEq following provider.realization ∧ HEq reference provider.towerModel ∧
          ∃ (model : Shared.Model (reader := OwnerReader.reconciled following reference)
              shared following reference),
        ∃ result, runReconciled? catalog coefficients formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  obtain ⟨initial, initialModel⟩ := interpreted.model candidate installed
  have distinct : candidate.keys.Nodup := by
    rw [← initialModel]
    simpa only [BaseContext.RealPrefix.finish_signature] using initial.realization.keys_nodup
  have success := SharedBase.chooseReconciled?_success catalog (owners.map (·.origin.base))
    candidate installed distinct (by
      intro source member
      obtain ⟨owner, present, rfl⟩ := List.mem_map.mp member
      exact ⟨(compatible owner present).1, (compatible owner present).2.1⟩)
  have depth := depth_zero (fun owner present => (compatible owner present).2.2)
  cases chosen : SharedBase.chooseReconciled? catalog (owners.map (·.origin.base)) with
  | none => simp only [chosen, Option.isSome_none, Bool.false_eq_true] at success
  | some selected =>
    obtain ⟨entry, member, target⟩ := SharedBase.chooseReconciled?_target catalog _ selected chosen
    obtain ⟨provider, same⟩ := interpreted.model entry member
    have base_eq : selected.target = provider.context.finish := by
      rw [target, ← same, depth]
      rfl
    have realized : ∃ (following : selected.target.Realization)
        (reference : Model (Context.ofBase selected.target) ℝ),
        HEq following provider.realization ∧ HEq reference provider.towerModel := by
      rw [base_eq]
      exact ⟨provider.realization, provider.towerModel, HEq.rfl, HEq.rfl⟩
    obtain ⟨following, reference, history, interpretation⟩ := realized
    obtain ⟨shared, produced, ⟨model⟩⟩ :=
      Shared.gatherReconciled?_models following reference owners (by
        intro owner present
        exact selected.included owner.origin.base (List.mem_map.mpr ⟨owner, present, rfl⟩))
    have gathered := Shared.gatherReconciledFrom?_of_success catalog owners selected chosen
      shared produced
    obtain ⟨result, checked, semantic⟩ :=
      runReconciled?_spec catalog shared gathered model.target model.owners coefficients formula
        quantifier
    exact ⟨selected.target, shared, gathered, provider, same ▸ member, base_eq,
      following, reference, history, interpretation, model, result, checked, semantic⟩

/-- The ordinary-real production projection of the named catalog history.
The stronger `gather_history` retains the exact selected provider and its model. -/
theorem gather_reconciled (catalog : BaseContext.Catalog registry)
    (interpreted : catalog.Models)
    (candidate : BaseContext.RealPrefix registry) (installed : candidate ∈ catalog.prefixes)
    (compatible : ∀ owner ∈ owners,
      owner.origin.base.signature.constants.Nodup ∧
        owner.origin.base.signature.constants ⊆ candidate.keys ∧ owner.origin.base.depth = 0)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ (selected : BaseContext.PackedContext registry) (shared : Shared selected owners),
      Shared.gatherReconciledFrom? catalog owners = some ⟨selected, shared⟩ ∧
      ∃ (following : selected.Realization)
        (reference : Model (Context.ofBase selected) ℝ)
        (model : Shared.Model (reader := OwnerReader.reconciled following reference)
          shared following reference),
        ∃ result, runReconciled? catalog coefficients formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  obtain ⟨selected, shared, gathered, provider, installed, same, following, reference,
      history, interpretation, model, result, produced, semantic⟩ :=
    gather_history catalog interpreted candidate installed compatible coefficients formula quantifier
  exact ⟨selected, shared, gathered, following, reference, model, result, produced, semantic⟩

end Hex.RCF.RealCoefficients.Gather
