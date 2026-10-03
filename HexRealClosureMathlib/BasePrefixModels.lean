/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseProvider

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry}

/-- Retrieve an existing provider model from its actual realization history.
No bounds, progress proof or coefficient interpretation is reconstructed. -/
private noncomputable def RealChain.Realization.lookup
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) (keys : List ConstantKey) :
    Option (RealPrefix.Model registry) := by
  induction realization with
  | base => exact if keys = [] then some (RealPrefix.Model.rational registry) else none
  | step parent previous earlier key bounds registered sp ap τ contained transcendental ih =>
    exact if keys = parent.keys ++ [key] then
      some (.pack (.step parent key bounds registered sp ap)
        (parent.interpretStep previous key bounds registered sp ap τ contained transcendental)
        (.step parent previous earlier key bounds registered sp ap τ contained transcendental))
    else ih

/-- Resolve the requested ordered path in one immutable provider-derived model. -/
noncomputable def RealPrefix.Model.prefix? (model : Model registry)
    (keys : List ConstantKey) : Option (Model registry) := by
  cases model with
  | pack chain interpretation realization => exact realization.lookup keys

private theorem RealChain.Realization.lookup_keys
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) (keys : List ConstantKey)
    (found : RealPrefix.Model registry) (produced : realization.lookup keys = some found) :
    found.context.keys = keys := by
  induction realization with
  | base =>
    change (if keys = [] then some (RealPrefix.Model.rational registry) else none) =
      some found at produced
    split at produced
    · cases Option.some.inj produced
      simp only [RealPrefix.Model.rational, RealPrefix.Model.context, RealPrefix.keys,
        RealContext.keys, RealContext.ofChain_chain, RealChain.keys]
      symm
      assumption
    · contradiction
  | step parent previous earlier key bounds registered sp ap τ contained transcendental ih =>
    change (if keys = parent.keys ++ [key] then
      some (RealPrefix.Model.pack (.step parent key bounds registered sp ap)
        (parent.interpretStep previous key bounds registered sp ap τ contained transcendental)
        (.step parent previous earlier key bounds registered sp ap τ contained transcendental))
      else earlier.lookup keys) = some found at produced
    split at produced
    · cases Option.some.inj produced
      change (RealContext.ofChain (parent.step key bounds registered sp ap)).chain.keys = keys
      rw [RealContext.ofChain_chain]
      change parent.keys ++ [key] = keys
      symm
      assumption
    · exact ih produced

/-- A successful lookup returns the exact requested native predecessor path. -/
theorem RealPrefix.Model.prefix?_keys (model found : Model registry)
    (keys : List ConstantKey) (produced : model.prefix? keys = some found) :
    found.context.keys = keys := by
  cases model with
  | pack chain interpretation realization => exact realization.lookup_keys keys found produced

private theorem prefix_step (keys parent : List ConstantKey) (key : ConstantKey)
    (different : keys ≠ parent ++ [key]) : keys <+: parent ++ [key] ↔ keys <+: parent := by
  constructor
  · intro included
    have lengths := included.length_le
    have unequal : keys.length ≠ (parent ++ [key]).length := by
      intro same
      exact different (included.eq_of_length same)
    exact List.prefix_of_prefix_length_le included (List.prefix_append parent [key]) (by
      simp only [List.length_append, List.length_singleton] at lengths unequal
      omega)
  · exact List.prefix_append_of_prefix

private theorem RealChain.Realization.lookup_isSome
    {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → OrderedFn.Oracle.Bounds} {sign : K → Int}
    {chain : RealChain registry K approx sign}
    {model : (RealContext.ofChain chain).Interpretation}
    (realization : chain.Realization registry model) (keys : List ConstantKey) :
    (realization.lookup keys).isSome = true ↔ keys <+: chain.keys := by
  induction realization with
  | base =>
    change (if keys = [] then some (RealPrefix.Model.rational registry) else none).isSome =
      true ↔ keys <+: []
    by_cases same : keys = [] <;> simp [same, List.prefix_nil]
  | step parent previous earlier key bounds registered sp ap τ contained transcendental ih =>
    change (if keys = parent.keys ++ [key] then
      some (RealPrefix.Model.pack (.step parent key bounds registered sp ap)
        (parent.interpretStep previous key bounds registered sp ap τ contained transcendental)
        (.step parent previous earlier key bounds registered sp ap τ contained transcendental))
      else earlier.lookup keys).isSome = true ↔ keys <+: parent.keys ++ [key]
    by_cases same : keys = parent.keys ++ [key]
    · rw [ite_eq_left same]
      exact iff_of_true rfl (same ▸ List.prefix_refl _)
    · rw [ite_eq_right same]
      exact ih.trans (prefix_step keys parent.keys key same).symm

/-- Every ordered predecessor path has its stored provider model, and
unrelated paths are rejected. -/
theorem RealPrefix.Model.prefix?_isSome (model : Model registry) (keys : List ConstantKey) :
    (model.prefix? keys).isSome = true ↔ keys <+: model.context.keys := by
  cases model with
  | pack chain interpretation realization =>
    have success := realization.lookup_isSome keys
    simpa only [RealPrefix.Model.prefix?, RealPrefix.Model.context, RealPrefix.keys_pack,
      RealContext.keys, RealContext.ofChain_chain] using success

/-- The returned model owns the exact requested validated context, rather
than merely another context with compatible bounds. -/
theorem RealPrefix.Model.prefix?_context (model found : Model registry)
    (requested : RealPrefix registry)
    (produced : model.prefix? requested.keys = some found) :
    found.context = requested := RealPrefix.keys_inj (model.prefix?_keys found requested.keys produced)

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.prefix?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.prefix?_isSome

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.prefix?_context' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.prefix?_context
