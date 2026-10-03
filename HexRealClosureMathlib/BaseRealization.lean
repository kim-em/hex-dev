/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseInterpretation

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

variable {registry : Registry}

/-- The rational interpretation attached to the actual initial chain. -/
@[expose] noncomputable def RealChain.interpretBase (registry : Registry) :
    (RealContext.ofChain (RealChain.base (registry := registry))).Interpretation :=
  let model := RealContext.Interpretation.rational registry
  ⟨model.hom, model.sign, model.contains⟩

/-- Interpret one stored native step from the actual predecessor model and
the registered provider's real value. Progress remains the stored progress. -/
noncomputable def RealChain.interpretStep
    {K : Type} [g : Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealChain registry K approx sign)
    (model : (RealContext.ofChain parent).Interpretation)
    (key : ConstantKey) (bounds : Rat → Bounds) (registered : registry key = some bounds)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains (bounds δ) τ)
    (transcendental : letI : Field K := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) :
    (RealContext.ofChain (.step parent key bounds registered sp ap)).Interpretation := by
  have present : (registry key).isSome = true := by simp only [registered, Option.isSome_some]
  have provider : (registry key).get present = bounds := by simp only [registered]; rfl
  have sp' : ∀ f : RationalFn K,
      Acc (Next (Real.attempt ((RealContext.ofChain parent).source key present) f)) 0 := by
    simpa only [RealContext.source, provider] using sp
  have ap' : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt ((RealContext.ofChain parent).source key present) f
        (Real.requestWidth δ))) 0 := by
    simpa only [RealContext.source, provider] using ap
  have contained' : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ := by
    simpa only [provider] using contained
  let generated := model.constant key present sp' ap' τ contained' transcendental
  refine ⟨generated.hom, ?_, ?_⟩
  · intro f
    simpa only [RealContext.source, provider] using generated.sign f
  · intro f δ
    simpa only [RealContext.approx, RealContext.source, provider] using generated.contains f δ

/-- Provider-derived interpretations retain their entire predecessor chain.
The constructors request only the new provider's own semantic premises. -/
inductive RealChain.Realization (registry : Registry) :
    {K : Type} → [Lean.Grind.Field K] → [DecidableEq K] →
    {approx : K → Rat → Bounds} → {sign : K → Int} →
    (chain : RealChain registry K approx sign) →
    (RealContext.ofChain chain).Interpretation → Type 1
  | base : Realization registry .base (RealChain.interpretBase registry)
  | step {K : Type} [Lean.Grind.Field K] [DecidableEq K]
      {approx : K → Rat → Bounds} {sign : K → Int}
      (parent : RealChain registry K approx sign)
      (model : (RealContext.ofChain parent).Interpretation)
      (previous : Realization registry parent model)
      (key : ConstantKey) (bounds : Rat → Bounds) (registered : registry key = some bounds)
      (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
      (ap : ∀ (f : RationalFn K) (δ : Rat),
        Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0)
      (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains (bounds δ) τ)
      (transcendental : letI : Field K := HexPolyMathlib.fieldOfGrind
        Real.RelativeTranscendence model.hom τ) :
      Realization registry (.step parent key bounds registered sp ap)
        (RealChain.interpretStep parent model key bounds registered sp ap τ contained transcendental)

/-- The step's derived real embedding preserves every predecessor coefficient. -/
theorem RealChain.interpretStep_embed
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealChain registry K approx sign)
    (model : (RealContext.ofChain parent).Interpretation)
    (key : ConstantKey) (bounds : Rat → Bounds) (registered : registry key = some bounds)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt ⟨approx, bounds⟩ f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt ⟨approx, bounds⟩ f (Real.requestWidth δ))) 0)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains (bounds δ) τ)
    (transcendental : letI : Field K := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) (a : K) :
    (parent.interpretStep model key bounds registered sp ap τ contained transcendental).hom
      (RationalFn.C a) = model.hom a := by
  let : Field K := HexPolyMathlib.fieldOfGrind
  change RealModel.evalHom HexPolyMathlib.toGrind_fieldOfGrind transcendental
    (RationalFn.C a) = model.hom a
  exact RealModel.evalHom_C HexPolyMathlib.toGrind_fieldOfGrind transcendental a

/-- Interpretation of an actual packed real prefix, retaining its native field. -/
@[expose] def RealPrefix.Interpretation (entry : RealPrefix registry) : Type := by
  cases entry with
  | pack context => exact context.Interpretation

/-- Unpack the real embedding using the same native coefficient dictionary. -/
@[expose] noncomputable def RealPrefix.Interpretation.hom
    {entry : RealPrefix registry} (model : entry.Interpretation) :
    letI : Field entry.Carrier := HexPolyMathlib.fieldOfGrind
    entry.Carrier →+* ℝ := by
  cases entry with
  | pack context => exact RealContext.Interpretation.hom model

/-- The checked native prefix map preserves real values. The predecessor
agreement is derived through every registered step and uniqueness of bounds. -/
theorem RealChain.Realization.embedding
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (realization : target.Realization registry model)
    (source : RealPrefix registry) (original : source.Interpretation)
    (map : FieldEmbedding source.Carrier K) (produced : target.embedding? source = some map)
    (a : source.Carrier) : model.hom (map.value a) = original.hom a := by
  induction realization generalizing source with
  | base =>
    by_cases keys : source.keys = (RealChain.base (registry := registry)).keys
    · have same : source = .pack (RealContext.ofChain (.base (registry := registry))) :=
        RealPrefix.keys_inj (by simpa only [RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using keys)
      subst source
      rw [RealChain.embedding?_self] at produced
      cases produced
      rw [FieldEmbedding.identity_value]
      exact congrArg (fun hom => hom a) (RealContext.Interpretation.hom_unique _ original)
    · rw [RealChain.embedding?_base source keys] at produced
      contradiction
  | step parent parentModel previous key bounds registered sp ap τ contained transcendental ih =>
    by_cases keys : source.keys = (parent.step key bounds registered sp ap).keys
    · have same : source = .pack (RealContext.ofChain (parent.step key bounds registered sp ap)) :=
        RealPrefix.keys_inj (by simpa only [RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using keys)
      subst source
      rw [RealChain.embedding?_self] at produced
      cases produced
      rw [FieldEmbedding.identity_value]
      exact congrArg (fun hom => hom a) (RealContext.Interpretation.hom_unique _ original)
    · rw [RealChain.embedding?_step parent key bounds registered sp ap source keys] at produced
      cases found : parent.embedding? source with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        rw [FieldEmbedding.comp_value, FieldEmbedding.constants_value,
          RealChain.interpretStep_embed]
        exact ih source original previousMap found a

/-- Real-prefix transport preserves the signs computed by both actual native
contexts, using the provider-derived target and the original source model. -/
theorem RealChain.Realization.embedding_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (realization : target.Realization registry model)
    (source : RealContext registry S sourceApprox sourceSign) (original : source.Interpretation)
    (map : FieldEmbedding S K) (produced : target.embedding? (.pack source) = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  calc
    sign (map.value a) = sgn (model.hom (map.value a)) := model.sign _
    _ = sgn (original.hom a) := congrArg sgn
      (realization.embedding (.pack source) original map produced a)
    _ = sourceSign a := (original.sign a).symm

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealChain.interpretStep_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.interpretStep_embed

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.embedding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.embedding

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.embedding_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.embedding_sign
