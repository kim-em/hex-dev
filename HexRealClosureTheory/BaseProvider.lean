/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.BaseRealization

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

/-- A provider-derived model retains the exact native chain and every
predecessor interpretation used to construct it. -/
inductive RealPrefix.Model (registry : Registry) : Type 1
  | pack {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → Bounds} {sign : K → Int}
      (chain : RealChain registry K approx sign)
      (interpretation : (RealContext.ofChain chain).Interpretation)
      (realization : chain.Realization registry interpretation)

/-- The actual validated prefix carried by the model. -/
@[expose] def RealPrefix.Model.context {registry : Registry} (model : Model registry) :
    RealPrefix registry := by
  cases model with
  | pack chain interpretation realization => exact .pack (RealContext.ofChain chain)

/-- The real embedding and bounds of this same native prefix. -/
@[expose] noncomputable def RealPrefix.Model.interpretation
    {registry : Registry} (model : Model registry) : model.context.Interpretation := by
  cases model with
  | pack chain interpretation realization => exact interpretation

/-- Rational coefficients initialize the provider-derived model. -/
@[expose] noncomputable def RealPrefix.Model.rational (registry : Registry) : Model registry :=
  .pack .base (RealChain.interpretBase registry) .base

/-- Register a new provider against the model's actual predecessor. All search
progress, coefficient agreement and predecessor realization are derived here. -/
@[expose] noncomputable def RealPrefix.Model.register
    {registry : Registry} (parent : Model registry)
    (key : ConstantKey) (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) : Model registry := by
  cases parent with
  | @pack K field eq approx sign chain interpretation realization =>
    letI : Field K := HexPolyTheory.fieldOfGrind
    have compatible : Field.toGrindField (K := K) = field := HexPolyTheory.toGrind_fieldOfGrind
    let native := RealContext.ofChain chain
    let valid := interpretation.valid key present τ contained width transcendental
    let generated := native.registration compatible key present valid
    let child := chain.step key ((registry key).get present) (Option.eq_some_of_isSome present)
      generated.signProgress generated.approxProgress
    let following := chain.interpretStep interpretation key ((registry key).get present)
      (Option.eq_some_of_isSome present) generated.signProgress generated.approxProgress
      τ contained transcendental
    exact .pack child following (.step chain interpretation realization key
      ((registry key).get present) (Option.eq_some_of_isSome present)
      generated.signProgress generated.approxProgress τ contained transcendental)

/-- Registration records the actual predecessor path and the new immutable key. -/
theorem RealPrefix.Model.register_keys
    {registry : Registry} (parent : Model registry)
    (key : ConstantKey) (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    (parent.register key present τ contained width transcendental).context.keys =
      parent.context.keys ++ [key] := by
  cases parent
  simp only [RealPrefix.Model.register, RealPrefix.Model.context, RealPrefix.keys,
    RealContext.keys, RealContext.ofChain_chain]
  rfl

/-- The actual native inclusion agrees with both derived provider models.
Neither model supplies a separate coefficient-agreement hypothesis. -/
theorem RealPrefix.Model.embedding
    {registry : Registry} (source target : Model registry)
    (map : FieldEmbedding source.context.Carrier target.context.Carrier)
    (produced : source.context.embedding? target.context = some map)
    (a : source.context.Carrier) : target.interpretation.hom (map.value a) =
      source.interpretation.hom a := by
  cases source with
  | pack sourceChain sourceModel sourceProof =>
    cases target with
    | pack targetChain targetModel targetProof =>
      change (RealPrefix.pack (RealContext.ofChain sourceChain)).embedding?
        (.pack (RealContext.ofChain targetChain)) = some map at produced
      rw [RealPrefix.embedding?_ofChain] at produced
      exact targetProof.embedding (.pack (RealContext.ofChain sourceChain)) sourceModel map
        produced a

/-- Registration returns a prefix for which the actual native predecessor map
succeeds and preserves every real coefficient value. -/
theorem RealPrefix.Model.register_map
    {registry : Registry} (parent : Model registry)
    (key : ConstantKey) (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    let child := parent.register key present τ contained width transcendental
    ∃ map : FieldEmbedding parent.context.Carrier child.context.Carrier,
      parent.context.embedding? child.context = some map ∧
      ∀ a, child.interpretation.hom (map.value a) = parent.interpretation.hom a := by
  intro child
  have keys : parent.context.keys <+: child.context.keys := by
    rw [RealPrefix.Model.register_keys]
    exact List.prefix_append _ _
  have success := (RealPrefix.embedding?_isSome parent.context child.context).mpr keys
  cases produced : parent.context.embedding? child.context with
  | none => simp only [produced, Option.isSome_none, Bool.false_eq_true] at success
  | some map => exact ⟨map, rfl, fun a => parent.embedding child map produced a⟩

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.register

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.embedding

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.register_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.register_map
