/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseReconciliationModel
public import HexRealClosureMathlib.BaseFactory
import all HexRealClosureMathlib.BasePermutation

public section

namespace Hex.RealClosure.BaseContext

/-- A real field hom from the native rational-function field sends its formal
variable to a value transcendental over the hom's embedded coefficient field. -/
theorem hom_transcendence {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (f : letI : Field (RationalFn K) := HexPolyMathlib.fieldOfGrind
      RationalFn K →+* ℝ) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    OrderedFn.Real.RelativeTranscendence (f.comp (FieldEmbedding.constants K).hom) (f RationalFn.X) := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field (RationalFn K) := HexPolyMathlib.fieldOfGrind
  have evaluate (p : DensePoly K) :
      (HexPolyMathlib.toPolynomial p).eval₂ (f.comp (FieldEmbedding.constants K).hom) (f RationalFn.X) =
        f (RationalFn.ofPoly p) := by
    rw [HexPolyMathlib.eval₂_horner, ← FieldEmbedding.formal_eval,
      DensePoly.eval, DensePoly.Interpret.map_list]
    have loop (coefficients : List K) :
        coefficients.foldr (fun c acc => f (RationalFn.C c) + f RationalFn.X * acc) 0 =
          f (DensePoly.evalCoeffList (coefficients.map RationalFn.C) RationalFn.X) := by
      induction coefficients with
      | nil => exact f.map_zero.symm
      | cons c rest ih =>
        simp only [List.foldr_cons, List.map_cons, DensePoly.evalCoeffList,
          map_add, map_mul, ih]
        rw [mul_comm]
        exact add_comm _ _
    simpa only [RingHom.comp_apply, FieldEmbedding.hom_apply, FieldEmbedding.constants_value,
      DensePoly.toList, DensePoly.toArray] using loop p.toList
  intro polynomial nonzero vanished
  have same := evaluate (HexPolyMathlib.ofPolynomial polynomial)
  rw [HexPolyMathlib.toPolynomial_ofPolynomial] at same
  have nativeZero : RationalFn.ofPoly (HexPolyMathlib.ofPolynomial polynomial) = 0 :=
    f.injective (same.symm.trans (vanished.trans f.map_zero.symm))
  have denseZero : HexPolyMathlib.ofPolynomial polynomial = 0 := RationalFn.ofPoly_injective nativeZero
  apply nonzero
  rw [← HexPolyMathlib.toPolynomial_ofPolynomial polynomial, denseZero, HexPolyMathlib.toPolynomial_zero]

/-- Reconstruct the actual predecessor realizations from a field hom and
provider containment at every native generator. The original chains supply
their stored progress proofs; no new analytic or coefficient laws are assumed. -/
theorem RealChain.realize {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign)
    (f : letI : Field K := HexPolyMathlib.fieldOfGrind; K →+* ℝ)
    (providers : ∀ i : Fin chain.keys.length,
      ∃ bounds, registry chain.keys.reverse[i] = some bounds ∧
        ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (bounds δ)
          (f (chain.decode.value (BaseTower.generator chain.keys.length i i.isLt)))) :
    ∃ model : (RealContext.ofChain chain).Interpretation,
      Nonempty (chain.Realization registry model) ∧ model.hom = f := by
  induction chain with
  | base =>
    refine ⟨RealChain.interpretBase registry, ⟨.base⟩, ?_⟩
    let native : Rat →+* ℝ :=
      { toFun := f
        map_zero' := f.map_zero
        map_one' := f.map_one
        map_add' := f.map_add
        map_mul' := f.map_mul }
    let canonical : Rat →+* ℝ :=
      { toFun := (RealChain.interpretBase registry).hom
        map_zero' := (RealChain.interpretBase registry).hom.map_zero
        map_one' := (RealChain.interpretBase registry).hom.map_one
        map_add' := (RealChain.interpretBase registry).hom.map_add
        map_mul' := (RealChain.interpretBase registry).hom.map_mul }
    ext a
    exact DFunLike.congr_fun (RingHom.ext_rat canonical native) a
  | @step S field eq sourceApprox sourceSign parent key bounds registered sp ap ih =>
    letI : Field S := HexPolyMathlib.fieldOfGrind
    letI : Field (RationalFn S) := HexPolyMathlib.fieldOfGrind
    let restriction := f.comp (FieldEmbedding.constants S).hom
    have keys : (parent.step key bounds registered sp ap).keys = parent.keys ++ [key] := rfl
    have depth : parent.keys.length + 1 = (parent.step key bounds registered sp ap).keys.length := by
      change parent.keys.length + 1 = (parent.keys ++ [key]).length
      simp only [List.length_append, List.length_singleton]
    have earlier : ∀ i : Fin parent.keys.length,
        ∃ provider, registry parent.keys.reverse[i] = some provider ∧
          ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (provider δ)
            (restriction (parent.decode.value (BaseTower.generator parent.keys.length i i.isLt))) := by
      intro i
      obtain ⟨provider, member, inside⟩ := providers ⟨i + 1, by omega⟩
      refine ⟨provider, ?_, ?_⟩
      · simpa only [keys, List.reverse_append, List.reverse_singleton,
          List.singleton_append, Fin.getElem_fin, List.getElem_cons_succ] using member
      · intro δ positive
        have contains := inside δ positive
        rw [RealChain.decode, lifted_inner _ depth i] at contains
        simpa only [restriction, RingHom.comp_apply, FieldEmbedding.hom_apply,
          FieldEmbedding.constants_value] using contains
    obtain ⟨parentModel, ⟨previous⟩, coefficientHom⟩ := ih restriction earlier
    obtain ⟨provider, member, inside⟩ := providers ⟨0, by omega⟩
    have member' : registry key = some provider := by
      simpa only [keys, List.reverse_append, List.reverse_singleton,
        List.singleton_append, Fin.getElem_fin, List.getElem_cons_zero] using member
    have sameBounds : provider = bounds := Option.some.inj (member'.symm.trans registered)
    subst provider
    have contained : ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (bounds δ) (f RationalFn.X) := by
      intro δ positive
      have contains := inside δ positive
      rw [RealChain.decode, lifted_outer _ depth] at contains
      exact contains
    have transcendental : OrderedFn.Real.RelativeTranscendence parentModel.hom (f RationalFn.X) := by
      rw [coefficientHom]
      exact hom_transcendence f
    let model := parent.interpretStep parentModel key bounds registered sp ap
      (f RationalFn.X) contained transcendental
    refine ⟨model, ⟨.step parent parentModel previous key bounds registered sp ap
      (f RationalFn.X) contained transcendental⟩, ?_⟩
    apply real_hom_ext
    · intro a
      rw [RealChain.interpretStep_embed, coefficientHom]
      simp only [restriction, RingHom.comp_apply, FieldEmbedding.hom_apply,
        FieldEmbedding.constants_value]
    · exact RealChain.interpretStep_X _ _ _ _ _ _ _ _ _ _

/-- The target's actual provider realization reconstructs a reordered source
from the native factory's checked generator bindings and its stored progress. -/
theorem RealChain.Realization.reconstruct
    {registry : Registry} {K S : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field S] [DecidableEq S]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {sourceApprox : S → Rat → OrderedFn.Oracle.Bounds} {sourceSign : S → Int}
    {target : RealChain registry K approx sign}
    {targetModel : (RealContext.ofChain target).Interpretation}
    (following : target.Realization registry targetModel)
    (source : RealChain registry S sourceApprox sourceSign)
    (map : FieldEmbedding S K) (produced : target.reorder? source = some map) :
    ∃ original : (RealContext.ofChain source).Interpretation,
      Nonempty (source.Realization registry original) ∧
        original.hom = targetModel.hom.comp map.hom := by
  letI : Field S := HexPolyMathlib.fieldOfGrind
  letI : Field K := HexPolyMathlib.fieldOfGrind
  rw [RealChain.reorder?] at produced
  cases accepted : BaseTower.Inclusion.make? source.keys target.keys with
  | none => simp only [accepted, Option.map_none] at produced; contradiction
  | some inclusion =>
    simp only [accepted, Option.map_some, Option.some.injEq] at produced
    subst map
    apply source.realize
    intro i
    obtain ⟨j, sameKey, image⟩ := inclusion.binding i
    obtain ⟨bounds, member, inside⟩ := following.slot_provider j
    refine ⟨bounds, ?_, ?_⟩
    · rw [sameKey]
      exact member
    · intro δ positive
      simp only [RingHom.comp_apply, FieldEmbedding.hom_apply, FieldEmbedding.comp_value]
      have encoded : source.encode.value
          (source.decode.value (BaseTower.generator source.keys.length i i.isLt)) =
            BaseTower.generator source.keys.length i i.isLt := by
        rw [← FieldEmbedding.comp_value, source.encode_decode, FieldEmbedding.identity_value]
      rw [encoded, image]
      exact inside δ positive

/-- Derive a requested provider presentation from the target's actual model,
checking native reordering and retaining the source's stored progress proofs. -/
noncomputable def RealPrefix.Model.reconstruct? {registry : Registry}
    (following : Model registry) (source : RealPrefix registry) : Option (Model registry) := by
  classical
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      exact if compatible : (target.reorder? source.chain).isSome = true then
        let map := (target.reorder? source.chain).get compatible
        let available := proof.reconstruct source.chain map (Option.some_get compatible).symm
        let original := available.choose
        let realization := Classical.choice available.choose_spec.1
        some (.pack source.chain original realization)
      else none

/-- Reconstruction retains exactly the source's requested provider keys. -/
theorem RealPrefix.Model.reconstruct?_keys {registry : Registry}
    (following found : Model registry) (source : RealPrefix registry)
    (produced : following.reconstruct? source = some found) : found.context.keys = source.keys := by
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      dsimp only [RealPrefix.Model.reconstruct?] at produced
      split at produced
      · cases Option.some.inj produced
        change (RealContext.ofChain source.chain).chain.keys = source.chain.keys
        rw [RealContext.ofChain_chain]
      · contradiction

/-- Source reconstruction succeeds precisely at the native distinct-key and
key-inclusion boundary. -/
theorem RealPrefix.Model.reconstruct?_isSome {registry : Registry}
    (following : Model registry) (source : RealPrefix registry) :
    (following.reconstruct? source).isSome = true ↔
      source.keys.Nodup ∧ following.context.keys.Nodup ∧ source.keys ⊆ following.context.keys := by
  cases following with
  | pack target model proof =>
    cases source with
    | pack source =>
      dsimp only [RealPrefix.Model.reconstruct?]
      split
      · simp only [Option.isSome_some, true_iff]
        simpa only [RealPrefix.Model.context, RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using (target.reorder?_isSome source.chain).mp (by assumption)
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        simpa only [RealPrefix.Model.context, RealPrefix.keys_pack, RealContext.keys,
          RealContext.ofChain_chain] using
          not_congr (target.reorder?_isSome source.chain) |>.mp (by assumption)

private theorem reconstructed_prefix {registry : Registry} (model : RealPrefix.Model registry)
    (context : PackedContext registry)
    (keys : model.context.keys = context.signature.constants) :
    model.context.finish.extend context.signature.infinitesimals = context := by
  apply PackedContext.signature_inj
  rw [PackedContext.extend_signature, RealPrefix.finish_signature, keys]
  simp only [Nat.zero_add]

/-- Rebuild an actual source base from the target's provider realization and
its native key/depth checks. Infinitesimals remain successive formal variables. -/
noncomputable def PackedContext.Realization.reconstruct? {registry : Registry}
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry) : Option source.Realization :=
  if source.signature.infinitesimals ≤ target.signature.infinitesimals then
    (following.provider.reconstruct? source.realPrefix).attach.map fun found =>
      let model := found.val
      let produced := Option.mem_def.mp found.property
      let keys := (following.provider.reconstruct?_keys model source.realPrefix produced).trans
        (PackedContext.prefix_keys source)
      reconstructed_prefix model source keys ▸ model.staged source.signature.infinitesimals
  else none

/-- Source-base reconstruction checks exactly the provider inclusion and
infinitesimal depth required by accepted reconciled maps into this target. -/
theorem PackedContext.Realization.reconstruct?_isSome {registry : Registry}
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry) :
    (following.reconstruct? source).isSome = true ↔
      source.signature.constants.Nodup ∧ source.signature.constants ⊆ target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  have packaged : (following.reconstruct? source).isSome =
      if source.signature.infinitesimals ≤ target.signature.infinitesimals then
        (following.provider.reconstruct? source.realPrefix).isSome else false := by
    unfold PackedContext.Realization.reconstruct?
    split
    · rw [Option.isSome_map, Option.isSome_attach]
    · rfl
  rw [packaged]
  by_cases depth : source.signature.infinitesimals ≤ target.signature.infinitesimals <;>
    simp [depth, RealPrefix.Model.reconstruct?_isSome, PackedContext.prefix_keys,
      following.provider_keys, following.keys_nodup]

/-- Every accepted native reconciled map into an actual realized target
supplies a source realization, with no source interpretation premise. -/
theorem PackedContext.Realization.reconstruct?_accepted {registry : Registry}
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry)
    (accepted : (source.reconcile? target).isSome = true) :
    (following.reconstruct? source).isSome = true :=
  (following.reconstruct?_isSome source).mpr
    ((source.reconcile?_isSome target following.keys_nodup).mp accepted)

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower.BaseReconciliation

variable {registry : BaseContext.Registry} {source target : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R]

/-- Derive source coefficients using only the target's actual provider history,
the native accepted reconciliation and the supplied target field model. -/
noncomputable def Model.deriveCanonical (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) : Model (R := R) inclusion :=
  let accepted : (source.reconcile? target).isSome = true := by rw [inclusion.produced]; rfl
  let success := following.reconstruct?_accepted source accepted
  let original := (following.reconstruct? source).get success
  Model.derive source target original following inclusion targetModel

/-- Canonical source reconstruction retains the supplied target model exactly. -/
theorem Model.deriveCanonical_target (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.deriveCanonical following inclusion targetModel).target = targetModel := by
  unfold Model.deriveCanonical
  exact Model.derive_target _ _ _ _ _ _

/-- Target-only source reconstruction commutes with the next native base
inclusion whenever its actual target models preserve constants. -/
theorem Model.next_value
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S]
    (base : BaseContext.Context registry B sign)
    (old : BaseReconciliation source (.pack base))
    (next : BaseReconciliation source (.pack base.infinitesimal))
    (original : (BaseContext.PackedContext.pack base).Realization)
    (following : (BaseContext.PackedContext.pack base.infinitesimal).Realization)
    (oldModel : Tower.Model (Context.ofBase (.pack base)) R)
    (nextModel : Tower.Model (Context.ofBase (.pack base.infinitesimal)) S)
    (embedding : R →+* S)
    (constants : ∀ a, nextModel.value (BaseContext.Element.embed a) =
      embedding (oldModel.value a))
    (a : (Context.ofBase source).Value) :
    (Model.deriveCanonical following next nextModel).source.value a =
      embedding ((Model.deriveCanonical original old oldModel).source.value a) := by
  have depth := ((source.reconcile?_isSome (.pack base) original.keys_nodup).mp
    (by rw [old.produced]; rfl)).2.2
  rw [← (Model.deriveCanonical following next nextModel).value,
    Model.deriveCanonical_target, BaseReconciliation.next_value base old next depth]
  have preserved := (Model.deriveCanonical original old oldModel).value a
  rw [Model.deriveCanonical_target] at preserved
  exact (constants (old.value a)).trans (congrArg embedding preserved)

/-- The reconstructed source model is the ordered image of the previous
canonical source model, with no additional source agreement premise. -/
theorem Model.next
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S]
    (base : BaseContext.Context registry B sign)
    (old : BaseReconciliation source (.pack base))
    (next : BaseReconciliation source (.pack base.infinitesimal))
    (original : (BaseContext.PackedContext.pack base).Realization)
    (following : (BaseContext.PackedContext.pack base.infinitesimal).Realization)
    (oldModel : Tower.Model (Context.ofBase (.pack base)) R)
    (nextModel : Tower.Model (Context.ofBase (.pack base.infinitesimal)) S)
    (embedding : R →+* S) (ordered : StrictMono embedding)
    (constants : ∀ a, nextModel.value (BaseContext.Element.embed a) =
      embedding (oldModel.value a)) :
    (Model.deriveCanonical following next nextModel).source =
      (Model.deriveCanonical original old oldModel).source.map embedding ordered := by
  apply Tower.Model.value_ext
  intro a
  exact Model.next_value base old next original following oldModel nextModel embedding constants a

/-- A supplied source realization gives exactly the same source model as
reconstruction from the target; the native map fixes its interpretation. -/
theorem Model.derive_source (original : source.Realization) (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive source target original following inclusion targetModel).source =
      (Model.deriveCanonical following inclusion targetModel).source := by
  apply Tower.Model.value_ext
  intro a
  rw [← (Model.derive source target original following inclusion targetModel).value,
    Model.derive_target]
  have preserved := (Model.deriveCanonical following inclusion targetModel).value a
  rw [Model.deriveCanonical_target] at preserved
  exact preserved

/-- At an available ordered inclusion, the derived source interpretation is
identical to the existing ordered factory's source model. -/
theorem Model.deriveCanonical_ordered (following : target.Realization)
    (reconciled : BaseReconciliation source target) (ordered : BaseInclusion source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.deriveCanonical following reconciled targetModel).source =
      (BaseInclusion.Model.derive following ordered targetModel).source := by
  apply Tower.Model.value_ext
  intro a
  rw [← (Model.deriveCanonical following reconciled targetModel).value,
    Model.deriveCanonical_target, BaseReconciliation.value_eq_ordered reconciled ordered]
  have preserved := (BaseInclusion.Model.derive following ordered targetModel).value a
  rw [BaseInclusion.Model.derive_target] at preserved
  exact preserved

end Hex.RealClosure.Tower.BaseReconciliation

/-- info: 'Hex.RealClosure.BaseContext.hom_transcendence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.hom_transcendence

/-- info: 'Hex.RealClosure.BaseContext.RealChain.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.realize

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.reconstruct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.reconstruct

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?_keys

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.reconstruct?_isSome

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?_isSome

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?_accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.reconstruct?_accepted

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical_target

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.deriveCanonical_ordered

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.derive_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.derive_source

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.next_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.next_value

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.next
