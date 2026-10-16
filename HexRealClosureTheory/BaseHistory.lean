/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseHistory
public import HexRealClosureTheory.BaseProvider

public section
namespace Hex.RealClosure.BaseContext
open OrderedFn OrderedFn.Oracle

/-- The semantic premises of a new registered provider refer to the actual
interpretation of this constructed predecessor. Search progress is already
retained in `step`; no model of the final history is an input. -/
def RealPrefix.Model.StepCorrect {registry : Registry} (parent : RealPrefix.Model registry)
    (key : ConstantKey) (step : parent.context.Step key) : Prop :=
  ∃ τ : ℝ,
    (∀ δ, 0 < δ → Contains ((registry key).get step.present δ) τ) ∧
    (letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind;
      Real.RelativeTranscendence parent.interpretation.hom τ)

/-- Interpret the native step with the already delivered selected predecessor
and registered-provider interpretation. This uses no real-closure existence. -/
noncomputable def RealPrefix.Model.append {registry : Registry}
    (parent : RealPrefix.Model registry) (key : ConstantKey) (step : parent.context.Step key)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get step.present δ) τ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) : RealPrefix.Model registry := by
  cases parent with
  | pack chain interpretation realization =>
    let child := chain.step key ((registry key).get step.present)
      (Option.eq_some_of_isSome step.present) step.signProgress step.approxProgress
    let following := chain.interpretStep interpretation key ((registry key).get step.present)
      (Option.eq_some_of_isSome step.present) step.signProgress step.approxProgress
      τ contained transcendental
    exact .pack child following (.step chain interpretation realization key
      ((registry key).get step.present) (Option.eq_some_of_isSome step.present)
      step.signProgress step.approxProgress τ contained transcendental)

/-- The constructed interpretation belongs to the exact returned native
context, including its original predecessor dictionaries and progress proofs. -/
theorem RealPrefix.Model.append_context {registry : Registry}
    (parent : RealPrefix.Model registry) (key : ConstantKey) (step : parent.context.Step key)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get step.present δ) τ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    (parent.append key step τ contained transcendental).context = parent.context.append key step := by
  apply RealPrefix.keys_inj
  rw [RealPrefix.append_keys]
  cases parent with
  | pack chain interpretation realization =>
    change (RealContext.ofChain (chain.step key ((registry key).get step.present)
      (Option.eq_some_of_isSome step.present) step.signProgress step.approxProgress)).chain.keys =
      (RealContext.ofChain chain).chain.keys ++ [key]
    rw [RealContext.ofChain_chain, RealContext.ofChain_chain]
    rfl

/-- Turn only a new provider's analytic premises into native progress at this
predecessor, reusing the existing registration theorem. -/
noncomputable def RealPrefix.Model.progress {registry : Registry}
    (parent : RealPrefix.Model registry) (key : ConstantKey) (present : (registry key).isSome = true)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) : parent.context.Step key := by
  cases parent with
  | @pack K field eq approx sign chain interpretation realization =>
    letI : Field K := HexPolyTheory.fieldOfGrind
    have compatible : Field.toGrindField (K := K) = field := HexPolyTheory.toGrind_fieldOfGrind
    let native := RealContext.ofChain chain
    let valid := interpretation.valid key present τ contained width transcendental
    let generated := native.registration compatible key present valid
    exact ⟨present, generated.signProgress, generated.approxProgress⟩

/-- Accepted successive construction has a provider model. Each new semantic
premise is checked against the model constructed so far, not against a supplied
joint target history. This also handles an empty list and duplicate keys. -/
theorem RealPrefix.Model.extend?_model {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (valid : ∀ (parent : RealPrefix.Model registry) (key : ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : RealPrefix.Model registry) (keys : List ConstantKey) {result : RealPrefix registry}
    (accepted : RealPrefix.extend? read parent.context keys = some result) :
    ∃ model : RealPrefix.Model registry, model.context = result := by
  induction keys generalizing parent result with
  | nil =>
    simp only [RealPrefix.extend?, Option.some.injEq] at accepted
    exact ⟨parent, accepted⟩
  | cons key rest ih =>
    simp only [RealPrefix.extend?] at accepted
    split at accepted
    · exact ih parent accepted
    · cases supplied : read parent.context key with
      | none => simp only [supplied, reduceCtorEq] at accepted
      | some step =>
        simp only [supplied] at accepted
        obtain ⟨τ, contained, transcendental⟩ := valid parent key step supplied
        let child := parent.append key step τ contained transcendental
        have same : child.context = parent.context.append key step :=
          parent.append_context key step τ contained transcendental
        have following : RealPrefix.extend? read child.context rest = some result := by
          rw [same]
          exact accepted
        exact ih child following

/-- The progress adapter retains the same provider's semantic premises. -/
theorem RealPrefix.Model.progress_correct {registry : Registry}
    (parent : RealPrefix.Model registry) (key : ConstantKey) (present : (registry key).isSome = true)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    parent.StepCorrect key (parent.progress key present τ contained width transcendental) := by
  exact ⟨τ, contained, transcendental⟩

/-- Construction succeeds when every new requested provider supplies progress
and semantic validity at each actual lawful predecessor. These premises concern
single steps; no installed target context or model is supplied. -/
theorem RealPrefix.Model.extend?_success {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (valid : ∀ (parent : RealPrefix.Model registry) (key : ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : RealPrefix.Model registry) (keys : List ConstantKey)
    (ready : ∀ (current : RealPrefix.Model registry) (key : ConstantKey), key ∈ keys →
      key ∉ current.context.keys → (read current.context key).isSome = true) :
    (RealPrefix.extend? read parent.context keys).isSome = true := by
  induction keys generalizing parent with
  | nil => rfl
  | cons key rest ih =>
    have following : ∀ (current : RealPrefix.Model registry) (next : ConstantKey), next ∈ rest →
        next ∉ current.context.keys → (read current.context next).isSome = true := by
      intro current next member absent
      exact ready current next (List.mem_cons_of_mem key member) absent
    unfold RealPrefix.extend?
    split
    · exact ih parent following
    · rename_i absent
      have existsStep := ready parent key (List.mem_cons_self) absent
      cases supplied : read parent.context key with
      | none => simp only [supplied, Option.isSome_none, Bool.false_eq_true] at existsStep
      | some step =>
        obtain ⟨τ, contained, transcendental⟩ := valid parent key step supplied
        let child := parent.append key step τ contained transcendental
        have same : child.context = parent.context.append key step :=
          parent.append_context key step τ contained transcendental
        change (RealPrefix.extend? read (parent.context.append key step) rest).isSome = true
        rw [← same]
        exact ih child following

/-- The native predecessor inclusion into the constructed history preserves
every old coefficient. Both interpretations are constructed from the same
registered providers, rather than supplied with an agreement hypothesis. -/
theorem RealPrefix.Model.extend?_embedding {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (valid : ∀ (parent : RealPrefix.Model registry) (key : ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : RealPrefix.Model registry) (keys : List ConstantKey) {result : RealPrefix registry}
    (accepted : RealPrefix.extend? read parent.context keys = some result) :
    ∃ model : RealPrefix.Model registry, model.context = result ∧
      ∃ map : FieldEmbedding parent.context.Carrier model.context.Carrier,
        parent.context.embedding? model.context = some map ∧
        ∀ a, model.interpretation.hom (map.value a) = parent.interpretation.hom a := by
  obtain ⟨model, same⟩ := parent.extend?_model read valid keys accepted
  have before : parent.context.keys <+: model.context.keys := by
    rw [same]
    exact RealPrefix.extend?_prefix read parent.context keys accepted
  have success := (RealPrefix.embedding?_isSome parent.context model.context).mpr before
  cases produced : parent.context.embedding? model.context with
  | none => simp only [produced, Option.isSome_none, Bool.false_eq_true] at success
  | some map =>
    exact ⟨model, same, map, produced, fun a => parent.embedding model map produced a⟩

end Hex.RealClosure.BaseContext
