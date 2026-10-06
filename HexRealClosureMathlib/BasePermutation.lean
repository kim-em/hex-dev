/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePermutation
public import HexRealClosureMathlib.BaseMap
public import HexRealClosureMathlib.BaseSubsequence
import all HexRealClosure.BasePresentation
import all HexRealClosure.BasePermutation
import all HexRealClosureMathlib.BaseSubsequence

public section

namespace Hex.RealClosure.BaseContext

/-- Real field interpretations of native rational functions are determined
by their coefficient and formal-variable images. No model for an entire
infinitesimal context is introduced. -/
theorem real_hom_ext {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    (first next : letI : Field (RationalFn K) := HexPolyMathlib.fieldOfGrind
      RationalFn K →+* ℝ)
    (coefficients : ∀ a : K, first (RationalFn.C a) = next (RationalFn.C a))
    (generator : first RationalFn.X = next RationalFn.X) : first = next := by
  letI : Field (RationalFn K) := HexPolyMathlib.fieldOfGrind
  have polynomial (p : DensePoly K) : first (RationalFn.ofPoly p) = next (RationalFn.ofPoly p) := by
    have loop (cs : List K) :
        first (DensePoly.evalCoeffList (cs.map RationalFn.C) RationalFn.X) =
          next (DensePoly.evalCoeffList (cs.map RationalFn.C) RationalFn.X) := by
      induction cs with
      | nil => exact first.map_zero.trans next.map_zero.symm
      | cons a cs ih =>
        simp only [List.map_cons, DensePoly.evalCoeffList, map_add, map_mul,
          ih, coefficients, generator]
    rw [← FieldEmbedding.formal_eval, DensePoly.eval, DensePoly.Interpret.map_list]
    exact loop p.toList
  ext f
  obtain ⟨d, nonzero, clears⟩ := FieldEmbedding.clear_denominators [f]
  obtain ⟨p, cleared⟩ := clears f (by simp)
  have denominator : first (RationalFn.ofPoly d) ≠ 0 := by
    intro vanished
    exact nonzero (RationalFn.ofPoly_injective
      (first.injective (vanished.trans first.map_zero.symm)))
  apply mul_right_cancel₀ denominator
  calc
    first f * first (RationalFn.ofPoly d) = first (RationalFn.ofPoly p) := by
      rw [← first.map_mul, cleared]
    _ = next (RationalFn.ofPoly p) := polynomial p
    _ = next f * first (RationalFn.ofPoly d) := by
      rw [polynomial d, ← next.map_mul, cleared]

/-- Real interpretations of a positional tower agree when all formal
variables have the same images. Rational coefficients are fixed by field laws. -/
theorem BaseTower.hom_ext (n : Nat)
    (first next : letI : Field (BaseTower n) := HexPolyMathlib.fieldOfGrind
      BaseTower n →+* ℝ)
    (images : ∀ i : Fin n,
      first (BaseTower.generator n i i.isLt) = next (BaseTower.generator n i i.isLt)) :
    first = next := by
  induction n with
  | zero =>
    let firstRat : Rat →+* ℝ :=
      { toFun := first
        map_zero' := first.map_zero
        map_one' := first.map_one
        map_add' := first.map_add
        map_mul' := first.map_mul }
    let nextRat : Rat →+* ℝ :=
      { toFun := next
        map_zero' := next.map_zero
        map_one' := next.map_one
        map_add' := next.map_add
        map_mul' := next.map_mul }
    ext a
    exact DFunLike.congr_fun (RingHom.ext_rat firstRat nextRat) a
  | succ n ih =>
    let restriction := (FieldEmbedding.constants (BaseTower n)).hom
    have coefficients : first.comp restriction = next.comp restriction := by
      apply ih
      intro i
      have same := images ⟨i + 1, Nat.succ_lt_succ i.isLt⟩
      simpa only [restriction, RingHom.comp_apply, FieldEmbedding.hom_apply,
        FieldEmbedding.constants_value, BaseTower.generator] using same
    apply real_hom_ext
    · intro a
      simpa only [restriction, RingHom.comp_apply, FieldEmbedding.hom_apply,
        FieldEmbedding.constants_value] using DFunLike.congr_fun coefficients a
    · simpa only [BaseTower.generator] using images ⟨0, by omega⟩

private theorem lifted_outer {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {m n : Nat} (map : FieldEmbedding (BaseTower m) K) (depth : m + 1 = n) :
    (depth ▸ (show FieldEmbedding (BaseTower (m + 1)) (RationalFn K) from
      map.rationalFunctions) : FieldEmbedding (BaseTower n) (RationalFn K)).value
        (BaseTower.generator n 0 (by omega)) =
      (RationalFn.X : RationalFn K) := by
  cases depth
  change map.rationalFunctions.value RationalFn.X = RationalFn.X
  exact FieldEmbedding.rationalFunctions_X map

private theorem lifted_inner {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {m n : Nat} (map : FieldEmbedding (BaseTower m) K) (depth : m + 1 = n) (i : Fin m) :
    (depth ▸ (show FieldEmbedding (BaseTower (m + 1)) (RationalFn K) from
      map.rationalFunctions) : FieldEmbedding (BaseTower n) (RationalFn K)).value
        (BaseTower.generator n (i + 1) (by omega)) =
      RationalFn.C (map.value (BaseTower.generator m i i.isLt)) := by
  cases depth
  change map.rationalFunctions.value (RationalFn.C (BaseTower.generator m i i.isLt)) = _
  rw [FieldEmbedding.rationalFunctions_value, RationalFn.mapCoeffs_C]

/-- Every positional generator denotes the real value contained in the
bounds of its exact registered provider. -/
theorem RealChain.Realization.slot_provider {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) (i : Fin chain.keys.length) :
    ∃ bounds, registry chain.keys.reverse[i] = some bounds ∧
      ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (bounds δ)
        (model.hom (chain.decode.value (BaseTower.generator chain.keys.length i i.isLt))) := by
  induction realization with
  | base =>
    change Fin 0 at i
    exact Fin.elim0 i
  | step parent parentModel previous key bounds registered sp ap τ contained transcendental ih =>
    have depth : parent.keys.length + 1 = (parent.step key bounds registered sp ap).keys.length := by
      change parent.keys.length + 1 = (parent.keys ++ [key]).length
      simp only [List.length_append, List.length_singleton]
    obtain ⟨index, bound⟩ := i
    cases index with
    | zero =>
      refine ⟨bounds, ?_, ?_⟩
      · change registry (parent.keys ++ [key]).reverse[0] = some bounds
        simpa only [List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.getElem_cons_zero] using registered
      · intro δ positive
        rw [RealChain.decode, lifted_outer, RealChain.interpretStep_X]
        exact contained δ positive
    | succ index =>
      have earlier : index < parent.keys.length := by omega
      obtain ⟨provider, member, inside⟩ := ih ⟨index, earlier⟩
      refine ⟨provider, ?_, ?_⟩
      · have inRange : index + 1 < (parent.keys ++ [key]).reverse.length := by
          simp only [List.length_reverse, List.length_append, List.length_singleton]
          omega
        change registry ((parent.keys ++ [key]).reverse[index + 1]'inRange) = some provider
        simpa only [List.reverse_append, List.reverse_singleton,
          List.singleton_append, List.getElem_cons_succ, Fin.getElem_fin] using member
      · intro δ positive
        rw [RealChain.decode, lifted_inner _ depth ⟨index, earlier⟩,
          RealChain.interpretStep_embed]
        exact inside δ positive

/-- The registered bounds of any provider already in a realized chain contain
at most one real value. This uses its original predecessor's stored progress. -/
theorem RealChain.Realization.provider_unique {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) (key : ConstantKey) (member : key ∈ chain.keys)
    (provider : Rat → OrderedFn.Oracle.Bounds) (registeredProvider : registry key = some provider)
    (τ σ : ℝ)
    (left : ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (provider δ) τ)
    (right : ∀ δ, 0 < δ → OrderedFn.Oracle.Contains (provider δ) σ) : τ = σ := by
  induction realization with
  | base => change key ∈ [] at member; cases member
  | step parent parentModel previous last bounds registered sp ap value contained transcendental ih =>
    change key ∈ parent.keys ++ [last] at member
    rcases List.mem_append.mp member with earlier | same
    · exact ih earlier
    · have sameKey := List.mem_singleton.mp same
      subst key
      have sameBounds : provider = bounds := Option.some.inj (registeredProvider.symm.trans registered)
      subst provider
      exact RealChain.provider_unique parent parentModel last bounds registered sp ap τ σ left right

/-- A checked key permutation retains the real image of every source variable.
Provider agreement follows from the immutable registry and stored progress. -/
theorem RealChain.Realization.reordered_slot {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    {source : RealChain registry K sourceApprox sourceSign}
    {target : RealChain registry L targetApprox targetSign}
    {original : (RealContext.ofChain source).Interpretation}
    {following : (RealContext.ofChain target).Interpretation}
    (first : source.Realization registry original) (next : target.Realization registry following)
    (permutation : BaseTower.Permutation source.keys target.keys) (i : Fin source.keys.length) :
    following.hom (target.decode.value
      (permutation.embedding.value (BaseTower.generator source.keys.length i i.isLt))) =
      original.hom (source.decode.value (BaseTower.generator source.keys.length i i.isLt)) := by
  obtain ⟨j, sameKey, image⟩ := permutation.binding i
  rw [image]
  obtain ⟨sourceBounds, sourceRegistered, sourceContains⟩ := first.slot_provider i
  obtain ⟨targetBounds, targetRegistered, targetContains⟩ := next.slot_provider j
  have registered : registry source.keys.reverse[i] = some targetBounds := by
    rw [sameKey]
    exact targetRegistered
  have sameBounds : sourceBounds = targetBounds :=
    Option.some.inj (sourceRegistered.symm.trans registered)
  subst targetBounds
  have present : source.keys.reverse[i] ∈ source.keys := by
    apply List.mem_reverse.mp
    simpa only [Fin.getElem_fin] using
      (List.getElem_mem (l := source.keys.reverse) (n := i.val)
        (by simpa only [List.length_reverse] using i.isLt))
  exact (first.provider_unique _ present sourceBounds sourceRegistered _ _
    sourceContains targetContains).symm

/-- A checked key permutation preserves every rational function in the actual
provider carriers, including inverses and fractions. -/
theorem RealChain.Realization.permutation {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    {source : RealChain registry K sourceApprox sourceSign}
    {target : RealChain registry L targetApprox targetSign}
    {original : (RealContext.ofChain source).Interpretation}
    {following : (RealContext.ofChain target).Interpretation}
    (first : source.Realization registry original) (next : target.Realization registry following)
    (permutation : BaseTower.Permutation source.keys target.keys) (a : K) :
    following.hom (target.decode.value (permutation.embedding.value (source.encode.value a))) =
      original.hom a := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field L := HexPolyMathlib.fieldOfGrind
  have same : (following.hom.comp target.decode.hom).comp permutation.embedding.hom =
      original.hom.comp source.decode.hom := by
    apply BaseTower.hom_ext source.keys.length
    intro i
    simp only [RingHom.comp_apply, FieldEmbedding.hom_apply]
    exact first.reordered_slot next permutation i
  have restored := congrArg (fun map : FieldEmbedding K K => map.value a) source.decode_encode
  simp only [FieldEmbedding.comp_value, FieldEmbedding.identity_value] at restored
  have equal := DFunLike.congr_fun same (source.encode.value a)
  simp only [RingHom.comp_apply, FieldEmbedding.hom_apply] at equal
  rw [restored] at equal
  exact equal

/-- The actual checked native reordering factory preserves real values. -/
theorem RealChain.Realization.reorder {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    {source : RealChain registry K sourceApprox sourceSign}
    {target : RealChain registry L targetApprox targetSign}
    {original : (RealContext.ofChain source).Interpretation}
    {following : (RealContext.ofChain target).Interpretation}
    (first : source.Realization registry original) (next : target.Realization registry following)
    (map : FieldEmbedding K L) (produced : target.reorder? source = some map) (a : K) :
    following.hom (map.value a) = original.hom a := by
  unfold RealChain.reorder? at produced
  cases found : BaseTower.Permutation.make? source.keys target.keys with
  | none => simp only [found, Option.map_none] at produced; contradiction
  | some permutation =>
    simp only [found, Option.map_some, Option.some.injEq] at produced
    subst map
    rw [FieldEmbedding.comp_value, FieldEmbedding.comp_value]
    exact first.permutation next permutation a

/-- Real-provider reordering preserves signs computed by the native contexts. -/
theorem RealChain.Realization.reorder_sign {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → OrderedFn.Oracle.Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → OrderedFn.Oracle.Bounds} {targetSign : L → Int}
    {source : RealChain registry K sourceApprox sourceSign}
    {target : RealChain registry L targetApprox targetSign}
    {original : (RealContext.ofChain source).Interpretation}
    {following : (RealContext.ofChain target).Interpretation}
    (first : source.Realization registry original) (next : target.Realization registry following)
    (map : FieldEmbedding K L) (produced : target.reorder? source = some map) (a : K) :
    targetSign (map.value a) = sourceSign a := by
  rw [following.sign, first.reorder next map produced a, ← original.sign]

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.real_hom_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.real_hom_ext

/-- info: 'Hex.RealClosure.BaseContext.BaseTower.hom_ext' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.BaseTower.hom_ext

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.slot_provider' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.slot_provider

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.provider_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.provider_unique

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.reorder' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.reorder

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.reorder_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.reorder_sign
