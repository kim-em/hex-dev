/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseStagedReorder
public import HexRealClosureMathlib.BasePermutation
public import HexRealClosureMathlib.BaseStagedSubsequence

public section

namespace Hex.RealClosure.BaseContext
open OrderedFn OrderedFn.Oracle
variable {registry : Registry}

/-- An actual provider realization cannot register the same key twice:
its fixed provider value would already lie in the predecessor field. -/
theorem RealChain.Realization.keys_nodup
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) : chain.keys.Nodup := by
  induction realization with
  | base => exact List.nodup_nil
  | @step S field eq approx sign parent parentModel previous key bounds registered sp ap τ contained transcendental ih =>
    have fresh : key ∉ parent.keys := by
      intro member
      obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp (List.mem_reverse.mpr member)
      have parentBound : i < parent.keys.length := by simpa only [List.length_reverse] using bound
      obtain ⟨provider, providerRegistered, inside⟩ := previous.slot_provider ⟨i, parentBound⟩
      have providerRegistered' : registry key = some provider := by
        simpa only [Fin.getElem_fin, equal] using providerRegistered
      have sameBounds : provider = bounds := Option.some.inj (providerRegistered'.symm.trans registered)
      subst provider
      let a := parent.decode.value (BaseTower.generator parent.keys.length i parentBound)
      have same : τ = parentModel.hom a :=
        previous.provider_unique key member bounds registered τ (parentModel.hom a) contained inside
      letI : Field S := HexPolyMathlib.fieldOfGrind
      have nonzero : Polynomial.X - Polynomial.C a ≠ 0 := Polynomial.X_sub_C_ne_zero a
      have nonvanishing := transcendental (Polynomial.X - Polynomial.C a) nonzero
      apply nonvanishing
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, same, sub_self]
    change (parent.keys ++ [key]).Nodup
    apply List.nodup_append.mpr
    refine ⟨ih, by simp, ?_⟩
    intro a member b singleton equal
    have same : b = key := List.mem_singleton.mp singleton
    exact fresh (equal.trans same ▸ member)

/-- Distinct provider keys remain invariant under successive infinitesimals. -/
theorem Chain.Realization.keys_nodup
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    {chain : Chain registry K sign} (realization : chain.Realization registry) :
    chain.signature.constants.Nodup := by
  induction realization with
  | real parent model previous => exact previous.keys_nodup
  | infinitesimal parent previous ih => exact ih

/-- Actual realizations supply provider distinctness for the native staged
factory; callers need only key inclusion and sufficient infinitesimal depth. -/
theorem Chain.Realization.reconcile_success
    {K L : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field L] [DecidableEq L] {sourceSign : K → Int} {targetSign : L → Int}
    {source : Chain registry K sourceSign} {target : Chain registry L targetSign}
    (original : source.Realization registry) (following : target.Realization registry)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (target.reconcile? source).isSome = true :=
  target.reconcile?_success source original.keys_nodup following.keys_nodup included depth

/-- The checked reordering map preserves signs through both actual provider
realizations and all retained or additional infinitesimal variables. -/
theorem Chain.Realization.reorder_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (realization : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.reorder? source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  induction realization generalizing S with
  | real targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change targetReal.reorder? sourceReal = some map at produced
      exact sourceProof.reorder_sign targetProof map produced a
    | infinitesimal sourceParent sourceProof =>
      change none = some map at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.reorder?.eq_def] at produced
      simp only [deeper, ↓reduceIte] at produced
      cases found : parent.reorder? source with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        rw [FieldEmbedding.comp_value]
        exact (FieldEmbedding.constants_sign _ previous.sign_zero previous.sign_one _).trans
          (ih source original previousMap found a)
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.reorder?.eq_def] at produced
        simp only [deeper, ↓reduceIte] at produced
        cases found : parent.reorder? sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          exact FieldEmbedding.rationalFunctions_sign previousMap _ _
            (fun b => ih sourceParent sourceProof previousMap found b) a

/-- Checked staged reorderings retain the prescribed real values of every
inherited provider coefficient, even between independently validated prefixes. -/
theorem Chain.Realization.reorder_realValue
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.reorder? source = some map)
    (a : S) (r : ℝ) (inherited : original.RealValue a r) :
    following.RealValue (map.value a) r := by
  induction following generalizing S with
  | real targetReal model targetProof =>
    cases original with
    | real sourceReal sourceModel sourceProof =>
      change targetReal.reorder? sourceReal = some map at produced
      change model.hom (map.value a) = r
      exact (sourceProof.reorder targetProof map produced a).trans inherited
    | infinitesimal sourceParent sourceProof =>
      change none = some map at produced
      contradiction
  | infinitesimal parent previous ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.reorder?.eq_def] at produced
      simp only [deeper, ↓reduceIte] at produced
      cases found : parent.reorder? source with
      | none => simp only [found, Option.map_none] at produced; contradiction
      | some previousMap =>
        simp only [found, Option.map_some, Option.some.injEq] at produced
        subst map
        exact ⟨previousMap.value a,
          by rw [FieldEmbedding.comp_value, FieldEmbedding.constants_value],
          ih source original previousMap found a inherited⟩
    · cases original with
      | real sourceReal sourceModel sourceProof =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent sourceProof =>
        rw [Chain.reorder?.eq_def] at produced
        simp only [deeper, ↓reduceIte] at produced
        cases found : parent.reorder? sourceParent with
        | none => simp only [found, Option.map_none] at produced; contradiction
        | some previousMap =>
          simp only [found, Option.map_some, Option.some.injEq] at produced
          subst map
          obtain ⟨b, same, real⟩ := inherited
          subst a
          refine ⟨previousMap.value b, ?_, ih sourceParent sourceProof previousMap found b real⟩
          rw [FieldEmbedding.rationalFunctions_value, RationalFn.mapCoeffs_C]

/-- Both the ordered fast path and the reordered path preserve actual native signs. -/
theorem Chain.Realization.reconcile_sign
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.reconcile? source = some map)
    (a : S) : sign (map.value a) = sourceSign a := by
  cases fast : target.subsequence? source with
  | none =>
    simp only [Chain.reconcile?, fast] at produced
    exact following.reorder_sign source original map produced a
  | some cached =>
    simp only [Chain.reconcile?, fast, Option.some.injEq] at produced
    subst map
    exact following.subsequence_sign source original cached fast a

/-- Reconciliation retains every inherited real-provider value through the
same original infinitesimal order and any additional target infinitesimals. -/
theorem Chain.Realization.reconcile_realValue
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    {target : Chain registry K sign} (following : target.Realization registry)
    (source : Chain registry S sourceSign) (original : source.Realization registry)
    (map : FieldEmbedding S K) (produced : target.reconcile? source = some map)
    (a : S) (r : ℝ) (inherited : original.RealValue a r) :
    following.RealValue (map.value a) r := by
  cases fast : target.subsequence? source with
  | none =>
    simp only [Chain.reconcile?, fast] at produced
    exact following.reorder_realValue source original map produced a r inherited
  | some cached =>
    simp only [Chain.reconcile?, fast, Option.some.injEq] at produced
    subst map
    exact following.subsequence_realValue source original cached fast a r inherited

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealChain.Realization.keys_nodup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.Realization.keys_nodup

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.reconcile_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.reconcile_success

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.reorder_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.reorder_sign

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.reorder_realValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.reorder_realValue

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.reconcile_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.reconcile_sign

/-- info: 'Hex.RealClosure.BaseContext.Chain.Realization.reconcile_realValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.Realization.reconcile_realValue
