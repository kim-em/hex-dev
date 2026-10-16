/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseContext

public section
namespace Hex.RealClosure.BaseContext
open OrderedFn OrderedFn.Oracle

/-- Progress of one registered provider at this exact native predecessor.
The companion derives these erased proofs from containment, width and
relative transcendence. No interpretation is a core constructor argument. -/
structure RealContext.Step {registry : Registry} {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (parent : RealContext registry K approx sign) (key : ConstantKey) : Type where
  present : (registry key).isSome = true
  signProgress : ∀ f : RationalFn K,
    Acc (Next (Real.attempt (parent.source key present) f)) 0
  approxProgress : ∀ (f : RationalFn K) (δ : Rat),
    Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0

/-- The same progress packet at a packed predecessor. -/
@[expose] def RealPrefix.Step {registry : Registry}
    (parent : RealPrefix registry) (key : ConstantKey) : Type := by
  cases parent with
  | pack context => exact RealContext.Step context key

/-- Availability of the provider in the same immutable registry. -/
theorem RealPrefix.Step.present {registry : Registry} {parent : RealPrefix registry}
    {key : ConstantKey} (step : parent.Step key) : (registry key).isSome = true := by
  cases parent with
  | pack context => exact RealContext.Step.present (parent := context) step

/-- Construct the actual next native prefix from its registered provider.
This calls the extension constructor; no installed target prefix is selected. -/
@[expose] def RealPrefix.append {registry : Registry} (parent : RealPrefix registry)
    (key : ConstantKey) (step : parent.Step key) : RealPrefix registry := by
  cases parent with
  | pack context =>
    exact .pack (context.constant key step.present step.signProgress step.approxProgress)

/-- Construction keeps the complete original path and appends the requested key. -/
theorem RealPrefix.append_keys {registry : Registry} (parent : RealPrefix registry)
    (key : ConstantKey) (step : parent.Step key) :
    (parent.append key step).keys = parent.keys ++ [key] := by
  cases parent with
  | pack context =>
    exact context.keys_constant key step.present step.signProgress step.approxProgress

/-- The native predecessor map is accepted for the newly constructed prefix. -/
theorem RealPrefix.append_embedding {registry : Registry} (parent : RealPrefix registry)
    (key : ConstantKey) (step : parent.Step key) :
    (parent.embedding? (parent.append key step)).isSome = true := by
  apply (RealPrefix.embedding?_isSome _ _).mpr
  rw [RealPrefix.append_keys]
  exact List.prefix_append _ _

/-- Build a missing history in the requested order. Existing keys reuse the
current prefix. Every new key asks for progress at the prefix just constructed;
missing progress rejects rather than selecting an unrelated installed history. -/
@[expose] def RealPrefix.extend? {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)) :
    (parent : RealPrefix registry) → List ConstantKey → Option (RealPrefix registry)
  | parent, [] => some parent
  | parent, key :: rest =>
    if key ∈ parent.keys then extend? read parent rest
    else match read parent key with
      | none => none
      | some step => extend? read (parent.append key step) rest

/-- A successful construction retains the original ordered provider history. -/
theorem RealPrefix.extend?_prefix {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) {result : RealPrefix registry}
    (accepted : RealPrefix.extend? read parent keys = some result) : parent.keys <+: result.keys := by
  induction keys generalizing parent result with
  | nil =>
    simp only [RealPrefix.extend?, Option.some.injEq] at accepted
    subst result
    exact List.prefix_refl _
  | cons key rest ih =>
    simp only [RealPrefix.extend?] at accepted
    split at accepted
    · exact ih (parent := parent) (result := result) accepted
    · cases supplied : read parent key with
      | none => simp only [supplied, reduceCtorEq] at accepted
      | some step =>
        simp only [supplied] at accepted
        have later := ih (parent := parent.append key step) (result := result) accepted
        have earlier : parent.keys <+: (parent.append key step).keys := by
          rw [RealPrefix.append_keys]
          exact List.prefix_append _ _
        exact earlier.trans later

/-- A successful history contains exactly the original and requested keys.
Skipping repeated keys never discards a requested provider. -/
theorem RealPrefix.extend?_mem {registry : Registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) {result : RealPrefix registry}
    (accepted : RealPrefix.extend? read parent keys = some result) (needle : ConstantKey) :
    needle ∈ result.keys ↔ needle ∈ parent.keys ∨ needle ∈ keys := by
  induction keys generalizing parent result with
  | nil =>
    simp only [RealPrefix.extend?, Option.some.injEq] at accepted
    subst result
    simp only [List.not_mem_nil, or_false]
  | cons key rest ih =>
    simp only [RealPrefix.extend?] at accepted
    split at accepted
    · rename_i present
      rw [ih parent accepted]
      simp only [List.mem_cons]
      constructor
      · intro h
        cases h with
        | inl h => exact Or.inl h
        | inr h => exact Or.inr (Or.inr h)
      · intro h
        rcases h with old | equal | later
        · exact Or.inl old
        · exact Or.inl (equal ▸ present)
        · exact Or.inr later
    · cases supplied : read parent key with
      | none => simp only [supplied, reduceCtorEq] at accepted
      | some step =>
        simp only [supplied] at accepted
        rw [ih (parent.append key step) accepted, RealPrefix.append_keys]
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, false_or, or_assoc]

end Hex.RealClosure.BaseContext
