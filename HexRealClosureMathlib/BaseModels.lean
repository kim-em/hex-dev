/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BasePrefixModels
public import HexRealClosureMathlib.BaseStagedRealization

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry}

/-- Provider-derived realization of one actual nominal staged base. -/
@[expose] def PackedContext.Realization (context : PackedContext registry) : Type 1 := by
  cases context with
  | pack context => exact context.chain.Realization registry

/-- Finishing a provider model retains its derived interpretation and every
actual predecessor, with no additional analytic premises. -/
noncomputable def RealPrefix.Model.realization (model : Model registry) :
    model.context.finish.Realization := by
  cases model with
  | pack chain interpretation realization =>
    change (Context.real (RealContext.ofChain chain)).chain.Realization registry
    rw [Context.real_chain, RealContext.ofChain_chain]
    exact .real chain interpretation realization

/-- Retain a nominal base's realization when adding its next infinitesimal. -/
noncomputable def PackedContext.Realization.infinitesimal
    {context : PackedContext registry} (original : context.Realization) :
    context.infinitesimal.Realization := by
  cases context with
  | pack context =>
    change context.infinitesimal.chain.Realization registry
    rw [Context.infinitesimal_chain]
    exact .infinitesimal context.chain original

/-- All requested infinitesimal stages are derived from the actual completed
provider model; each stage retains its native predecessor. -/
noncomputable def PackedContext.Realization.extend
    {context : PackedContext registry} (original : context.Realization) :
    (n : Nat) → (context.extend n).Realization
  | 0 => original
  | n + 1 => (original.extend n).infinitesimal

/-- Complete a provider model with any finite ordered infinitesimal suffix. -/
noncomputable def RealPrefix.Model.staged (model : Model registry) (n : Nat) :
    (model.context.finish.extend n).Realization := model.realization.extend n

private noncomputable def Chain.Realization.provider
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    {chain : Chain registry K sign} (realization : chain.Realization registry) :
    RealPrefix.Model registry := by
  induction realization with
  | real parent model previous => exact .pack parent model previous
  | infinitesimal parent previous ih => exact ih

private theorem Chain.Realization.provider_keys
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    {chain : Chain registry K sign} (realization : chain.Realization registry) :
    realization.provider.context.keys = chain.signature.constants := by
  induction realization with
  | real parent model previous =>
    change (RealContext.ofChain parent).chain.keys = parent.keys
    rw [RealContext.ofChain_chain]
  | infinitesimal parent previous ih => exact ih

/-- Retrieve the completed provider model retained by the actual staged base. -/
noncomputable def PackedContext.Realization.provider
    {context : PackedContext registry} (original : context.Realization) :
    RealPrefix.Model registry := by
  cases context with
  | pack context => exact Chain.Realization.provider original

/-- The retained provider history has the staged base's complete real-key path. -/
theorem PackedContext.Realization.provider_keys
    {context : PackedContext registry} (original : context.Realization) :
    original.provider.context.keys = context.signature.constants := by
  cases context with
  | pack context => exact Chain.Realization.provider_keys original

private theorem reconstruct_prefix (model : RealPrefix.Model registry)
    (context : PackedContext registry)
    (keys : model.context.keys = context.signature.constants) :
    model.context.finish.extend context.signature.infinitesimals = context := by
  apply PackedContext.signature_inj
  rw [PackedContext.extend_signature, RealPrefix.finish_signature, keys]
  simp only [Nat.zero_add]

/-- Derive an earlier base's realization from this target's actual provider
history. Compatibility is checked on the ordered real path and infinitesimal
depth; no duplicate provider premises or source interpretation are supplied. -/
noncomputable def PackedContext.Realization.restrict?
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry) : Option source.Realization :=
  if source.signature.infinitesimals ≤ target.signature.infinitesimals then
    (following.provider.prefix? source.signature.constants).attach.map fun found =>
      let model := found.val
      let produced := Option.mem_def.mp found.property
      let keys := following.provider.prefix?_keys model source.signature.constants produced
      reconstruct_prefix model source keys ▸ model.staged source.signature.infinitesimals
  else none

private theorem PackedContext.Realization.restrict?_isSome_proof
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry) :
    (following.restrict? source).isSome = true ↔
      source.signature.constants <+: target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  have packaged : (following.restrict? source).isSome =
      if source.signature.infinitesimals ≤ target.signature.infinitesimals then
        (following.provider.prefix? source.signature.constants).isSome else false := by
    unfold PackedContext.Realization.restrict?
    split
    · rw [Option.isSome_map, Option.isSome_attach]
    · rfl
  rw [packaged]
  by_cases depth : source.signature.infinitesimals ≤ target.signature.infinitesimals <;>
    simp [depth, RealPrefix.Model.prefix?_isSome, following.provider_keys]

/-- Deriving the source realization succeeds at exactly the native checked
base-inclusion boundary, including every compatible proper real prefix. -/
theorem PackedContext.Realization.restrict?_isSome
    {target : PackedContext registry} (following : target.Realization)
    (source : PackedContext registry) :
    (following.restrict? source).isSome = true ↔
      source.signature.constants <+: target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals :=
  following.restrict?_isSome_proof source

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.Model.staged' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.Model.staged

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.provider_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.provider_keys

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.restrict?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.restrict?

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.restrict?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.restrict?_isSome
