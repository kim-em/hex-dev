/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.Samples
public import HexRealClosureMathlib.CacheGather
public import HexRealClosure.SharedBase
public import HexRealClosureMathlib.BaseProvider

public section
open scoped List
namespace Hex.RCF.RealCoefficients.Gather
open Hex RealClosure RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {owners : List (Context registry)}

/-! Coordinates from independently constructed native contexts are transported
through the owner's actual gathering result. An ordinary-real common model
retains every original coordinate and selected embedding. This module composes
native production and shared syntax; source authentication and frozen replay
remain separate adapter obligations. -/

/-- Keep each coefficient at its original owner before applying its checked map. -/
@[expose] def values (shared : Shared base owners)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) :
    Fin owners.length → shared.input.context.Value :=
  fun i => shared.value i (coefficients i)

@[expose] noncomputable def valuation (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) (x : ℝ) :
    Fin (owners.length + 1) → ℝ :=
  RealFormula.append (fun i => (models.get i).1.value (coefficients i)) x

theorem values_real (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value) :
    (fun i => target.value (values shared coefficients i)) =
      (fun i => (models.get i).1.value (coefficients i)) := by
  funext i
  exact models.value i (coefficients i)

/-- Every original shared atom has its original owner's coordinate meaning
at the same real variable after gathering and specialization. -/
theorem prepare_eval (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (x : ℝ) :
    (RepresentationSpecialize.prepare (values shared coefficients) formula).map
      (RepresentationSpecialize.evaluate target.value target.zero_iff x) =
      formula.polys.map (fun q => q.eval (valuation shared target models coefficients x)) := by
  have result := Samples.prepare_real target (values shared coefficients) formula x
  simp only [Samples.valuation, values_real shared target models coefficients] at result
  exact result

/-- Native production in one gathered context retains all original owner coordinates.
The conclusion is shared syntax at one real variable, not frozen replay. -/
theorem run_spec (shared : Shared base owners)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (models.get i).1.value (coefficients i))) := by
  have result := Samples.run_spec target (values shared coefficients) formula quantifier
  rw [values_real shared target models coefficients] at result
  exact result

/-- A returned gathering result retains separately authenticated original
owner models. Factory equations establish their agreement with the common model. -/
theorem run_original (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (shared : Shared base owners) (produced : Shared.gather? base owners = some shared)
    (original : (i : Fin owners.length) → Model (owners[i]) ℝ)
    (sourceModels : ∀ i, (owners[i]).model? following reference = some (original i))
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (original i).value (coefficients i))) := by
  let model := Shared.Model.ofGather following reference owners shared produced
  have aligned : (fun i => model.target.value (values shared coefficients i)) =
      (fun i => (original i).value (coefficients i)) := by
    funext i
    exact model.value_of_model i (original i) (sourceModels i) (coefficients i)
  have result := Samples.run_spec model.target (values shared coefficients) formula quantifier
  rw [aligned] at result
  exact result

/-- Select a validated catalog base, retain the original coefficient order,
and run native sample production. Failure supplies no Boolean verdict. -/
@[expose] def runFrom? (catalog : BaseContext.Catalog registry)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    Option Bool :=
  match Shared.gatherFrom? catalog owners with
  | none => none
  | some ⟨_, shared⟩ => Samples.run (values shared coefficients) formula quantifier

/-- Automatic base selection preserves the same native decision and original
owner interpretations as explicit gathering. This is a production law. -/
theorem runFrom?_spec (catalog : BaseContext.Catalog registry)
    (shared : Shared base owners)
    (gathered : Shared.gatherFrom? catalog owners = some ⟨base, shared⟩)
    (target : Model shared.input.context ℝ) (models : Inclusions.Models target shared.maps)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, runFrom? catalog coefficients formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (models.get i).1.value (coefficients i))) := by
  obtain ⟨result, produced, semantic⟩ :=
    run_spec shared target models coefficients formula quantifier
  exact ⟨result, by simpa only [runFrom?, gathered, bind, Option.bind] using produced,
    semantic⟩

/-- Separately authenticated original models retain their exact coefficient
values after automatic selection. Their factory equations establish agreement;
there is no independent coefficient-agreement premise. -/
theorem runFrom?_original (catalog : BaseContext.Catalog registry)
    (following : base.Realization) (reference : Model (Context.ofBase base) ℝ)
    (shared : Shared base owners)
    (gathered : Shared.gatherFrom? catalog owners = some ⟨base, shared⟩)
    (original : (i : Fin owners.length) → Model (owners[i]) ℝ)
    (sourceModels : ∀ i, (owners[i]).model? following reference = some (original i))
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ result, runFrom? catalog coefficients formula quantifier = some result ∧
      (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
        (fun i => (original i).value (coefficients i))) := by
  obtain ⟨result, produced, semantic⟩ := run_original following reference shared
    (Shared.gatherFrom?_gathered catalog owners base shared gathered)
    original sourceModels coefficients formula quantifier
  exact ⟨result, by simpa only [runFrom?, gathered, bind, Option.bind] using produced,
    semantic⟩

/-- An installed, jointly validated prefix admits the original owners. Models
of the admissible installed prefixes supply the chosen real interpretation; no caller
chooses the target base or independent coefficient agreement. Every original
base has depth zero; symbolic infinitesimals need a separate finite realization.
This does not infer relative transcendence from separate registrations. -/
theorem gather_catalog (catalog : BaseContext.Catalog registry)
    (interpreted : ∀ entry ∈ catalog.prefixes,
      (∀ owner ∈ owners, owner.origin.base.signature.constants <+ entry.keys) →
      ∃ provider : BaseContext.RealPrefix.Model registry, provider.context = entry)
    (candidate : BaseContext.RealPrefix registry) (installed : candidate ∈ catalog.prefixes)
    (compatible : ∀ owner ∈ owners,
      owner.origin.base.signature.constants <+ candidate.keys ∧
        owner.origin.base.depth = 0)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ (selected : BaseContext.PackedContext registry) (shared : Shared selected owners),
      Shared.gatherFrom? catalog owners = some ⟨selected, shared⟩ ∧
      ∃ (following : selected.Realization)
        (reference : Model (Context.ofBase selected) ℝ)
        (model : Shared.Model shared following reference),
        ∃ result, runFrom? catalog coefficients formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  have success := SharedBase.choose?_success catalog (owners.map (·.origin.base))
    candidate installed (by
      intro source member
      obtain ⟨owner, present, rfl⟩ := List.mem_map.mp member
      exact (compatible owner present).1)
  have depth : SharedBase.depth (owners.map (·.origin.base)) = 0 := by
    have fold : ∀ sources : List (BaseContext.PackedContext registry),
        (∀ source ∈ sources, source.depth = 0) →
        sources.foldl (fun n source => max n source.depth) 0 = 0 := by
      intro sources
      induction sources with
      | nil => intro _; rfl
      | cons first rest ih =>
          intro zero
          rw [List.foldl_cons, zero first (by simp), Nat.max_self]
          exact ih (fun source member => zero source (List.mem_cons_of_mem first member))
    apply fold
    intro source member
    obtain ⟨owner, present, rfl⟩ := List.mem_map.mp member
    exact (compatible owner present).2
  cases chosen : SharedBase.choose? catalog (owners.map (·.origin.base)) with
  | none => simp only [chosen, Option.isSome_none, Bool.false_eq_true] at success
  | some selected =>
    obtain ⟨entry, member, target⟩ := SharedBase.choose?_target catalog _ selected chosen
    obtain ⟨provider, same⟩ := interpreted entry member (by
      intro owner present
      have keys := (SharedBase.compatible selected owner.origin.base
        (List.mem_map.mpr ⟨owner, present, rfl⟩)).1
      rw [target] at keys
      simpa only [BaseContext.PackedContext.extend_signature,
        BaseContext.RealPrefix.finish_signature] using keys)
    have realized : ∃ following : selected.target.Realization,
        Nonempty (Model (Context.ofBase selected.target) ℝ) := by
      rw [target, ← same, depth]
      exact ⟨provider.realization, ⟨provider.towerModel⟩⟩
    obtain ⟨following, ⟨reference⟩⟩ := realized
    obtain ⟨shared, produced, ⟨model⟩⟩ :=
      Shared.gather?_models following reference owners (by
        intro owner present
        exact SharedBase.compatible selected owner.origin.base
          (List.mem_map.mpr ⟨owner, present, rfl⟩))
    have gathered := Shared.gatherFrom?_of_success catalog owners selected chosen shared produced
    obtain ⟨result, checked, semantic⟩ :=
      runFrom?_spec catalog shared gathered model.target model.owners coefficients formula quantifier
    exact ⟨selected.target, shared, gathered, following, reference, model, result, checked, semantic⟩

/-- Ordered subsequences of registered constants suffice for actual gathering
and decision production. Every coefficient keeps its original owner's meaning;
additional target constants need not occur after the source constants. -/
theorem gather_subsequence (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ shared : Shared base owners, Shared.gather? base owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
        ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) := by
  obtain ⟨shared, produced, ⟨model⟩⟩ :=
    Shared.gather?_models following reference owners compatible
  obtain ⟨result, accepted, semantic⟩ :=
    run_spec shared model.target model.owners coefficients formula quantifier
  exact ⟨shared, produced, model, result, accepted, semantic⟩

/-- Prefix-compatible callers retain their original gathering and decision API. -/
theorem gather_spec (following : base.Realization)
    (reference : Model (Context.ofBase base) ℝ)
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (coefficients : (i : Fin owners.length) → (owners[i]).Value)
    (formula : RealFormula.QF (owners.length + 1)) (quantifier : RealFormula.Quantifier) :
    ∃ shared : Shared base owners, Shared.gather? base owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
        ∃ result, Samples.run (values shared coefficients) formula quantifier = some result ∧
          (result = true ↔ (RealFormula.Prenex.quant quantifier (.matrix formula)).toProp
            (fun i => (model.owners.get i).1.value (coefficients i))) :=
  gather_subsequence following reference
    (fun source member => ⟨(compatible source member).1.sublist,
      (compatible source member).2⟩) coefficients formula quantifier

end Hex.RCF.RealCoefficients.Gather
