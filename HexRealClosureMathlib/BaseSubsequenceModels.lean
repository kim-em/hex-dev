/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseSubsequence
public import HexRealClosureMathlib.BaseMap

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

/-- Relative transcendence restricts along an injective coefficient embedding
whose real values agree with the original coefficient interpretation. -/
theorem FieldEmbedding.transcendence {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {original : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ}
    {following : letI : Field L := HexPolyMathlib.fieldOfGrind; L →+* ℝ} {τ : ℝ}
    (map : FieldEmbedding K L) (agreement : ∀ a, following (map.value a) = original a)
    (transcendental : letI : Field L := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence following τ) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence original τ := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field L := HexPolyMathlib.fieldOfGrind
  have same : following.comp map.hom = original := by
    ext a
    exact agreement a
  intro p nonzero
  have mapped : p.map map.hom ≠ 0 := by
    intro zero
    apply nonzero
    exact (Polynomial.map_injective map.hom map.hom.injective) (zero.trans (Polynomial.map_zero map.hom).symm)
  have result := transcendental (p.map map.hom) mapped
  simpa only [Polynomial.eval₂_map, same] using result

/-- Every actual source chain selected by the native subsequence factory has
its own provider realization. It uses the source's stored progress proofs and
the target's fixed provider values; no new analytic premise is requested. -/
theorem RealChain.Realization.restrict_subsequence
    {registry : Registry} {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {model : (RealContext.ofChain target).Interpretation}
    (following : target.Realization registry model)
    (source : RealChain registry S sourceApprox sourceSign)
    (map : FieldEmbedding S K) (produced : target.subsequence? source = some map) :
    ∃ original : (RealContext.ofChain source).Interpretation,
      Nonempty (source.Realization registry original) := by
  induction following generalizing S with
  | base =>
    cases source with
    | base => exact ⟨RealChain.interpretBase registry, ⟨.base⟩⟩
    | step sourceParent sourceKey sourceBounds sourceRegistered sourceSp sourceAp =>
      change none = some map at produced
      contradiction
  | step parent parentModel previous key bounds registered sp ap τ contained transcendental ih =>
    cases source with
    | base => exact ⟨RealChain.interpretBase registry, ⟨.base⟩⟩
    | step sourceParent sourceKey sourceBounds sourceRegistered sourceSp sourceAp =>
      by_cases same : sourceKey = key
      · subst sourceKey
        have sameBounds : sourceBounds = bounds :=
          Option.some.inj (sourceRegistered.symm.trans registered)
        subst sourceBounds
        rw [RealChain.subsequence?] at produced
        simp only [↓reduceIte] at produced
        cases found : parent.subsequence? sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          obtain ⟨original, ⟨sourceProof⟩⟩ := ih sourceParent previousMap found
          have agreement := previous.subsequence sourceProof previousMap found
          have sourceTranscendental := previousMap.transcendence agreement transcendental
          exact ⟨sourceParent.interpretStep original key bounds sourceRegistered sourceSp sourceAp
              τ contained sourceTranscendental,
            ⟨.step sourceParent original sourceProof key bounds sourceRegistered sourceSp sourceAp
              τ contained sourceTranscendental⟩⟩
      · rw [RealChain.subsequence?] at produced
        simp only [same, ↓reduceIte] at produced
        cases found : parent.subsequence?
            (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp) with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          exact ih (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp)
            previousMap found

/-- Restrict a provider model to an actual validated real subsequence. The
source retains its own progress proofs for every coefficient predecessor. -/
noncomputable def RealPrefix.Model.submodel? {registry : Registry}
    (following : Model registry) (source : RealPrefix registry) : Option (Model registry) := by
  classical
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      exact if compatible : (target.subsequence? source.chain).isSome = true then
        let map := (target.subsequence? source.chain).get compatible
        let available :=  proof.restrict_subsequence source.chain map (Option.some_get compatible).symm
        let original := available.choose
        let realization := Classical.choice available.choose_spec
        some (.pack source.chain original realization)
      else none

/-- The derived provider model owns exactly the requested native subsequence. -/
theorem RealPrefix.Model.submodel?_keys {registry : Registry}
    (following found : Model registry) (source : RealPrefix registry)
    (produced : following.submodel? source = some found) : found.context.keys = source.keys := by
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      dsimp only [RealPrefix.Model.submodel?] at produced
      split at produced
      · cases Option.some.inj produced
        change (RealContext.ofChain source.chain).chain.keys = source.chain.keys
        rw [RealContext.ofChain_chain]
      · contradiction

/-- Subsequence restriction succeeds at exactly the native key boundary. -/
theorem RealPrefix.Model.submodel?_isSome {registry : Registry}
    (following : Model registry) (source : RealPrefix registry) :
    (following.submodel? source).isSome = true ↔
      List.Sublist source.keys following.context.keys := by
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      dsimp only [RealPrefix.Model.submodel?]
      split
      · simp only [Option.isSome_some, true_iff]
        simpa only [RealPrefix.Model.context, RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using (target.subsequence?_isSome source.chain).mp (by assumption)
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        simpa only [RealPrefix.Model.context, RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using
          not_congr (target.subsequence?_isSome source.chain) |>.mp (by assumption)

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.FieldEmbedding.transcendence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.FieldEmbedding.transcendence

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.restrict_subsequence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.restrict_subsequence

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?_keys

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.submodel?_isSome
