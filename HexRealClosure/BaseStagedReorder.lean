/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePermutationTotal
public import HexRealClosure.BaseSubsequence

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle
variable {registry : Registry}

/-- Reconcile provider-variable order while retaining the order of all original
infinitesimals. Additional target infinitesimals include the predecessor as constants. -/
@[expose] def Chain.reorder? {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    Option (FieldEmbedding K L) :=
  match target with
  | @Chain.real _ B field eq approx sign targetReal =>
    match source with
    | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
      targetReal.reorder? sourceReal
    | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
      (none : Option (FieldEmbedding (RationalFn A) B))
  | @Chain.infinitesimal _ B field eq sign parent =>
    if source.signature.infinitesimals < parent.signature.infinitesimals + 1 then
      (parent.reorder? source).map fun previous =>
        previous.comp (FieldEmbedding.constants B)
    else
      match source with
      | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
        (none : Option (FieldEmbedding A (RationalFn B)))
      | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
        (parent.reorder? sourceParent).map FieldEmbedding.rationalFunctions

/-- Prefer the existing subsequence inclusion; only a failed ordered inclusion
runs the checked real-provider reordering factory. -/
@[expose] def Chain.reconcile? {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    Option (FieldEmbedding K L) :=
  match target.subsequence? source with
  | some map => some map
  | none => target.reorder? source

/-- Provider-key inclusion and sufficient infinitesimal depth guarantee that
the actual staged reordering factory produces a native embedding. -/
theorem Chain.reorder?_success {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign)
    (sourceUnique : source.signature.constants.Nodup)
    (targetUnique : target.signature.constants.Nodup)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (target.reorder? source).isSome = true := by
  induction target generalizing K with
  | real targetReal =>
    cases source with
    | real sourceReal =>
      exact targetReal.reorder?_success sourceReal sourceUnique targetUnique included
    | infinitesimal sourceParent =>
      change sourceParent.signature.infinitesimals + 1 ≤ 0 at depth
      omega
  | infinitesimal parent ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.reorder?.eq_def]
      simp only [deeper, ↓reduceIte, Option.isSome_map]
      exact ih source sourceUnique targetUnique included (by omega)
    · cases source with
      | real sourceReal =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent =>
        rw [Chain.reorder?]
        simp only [deeper, ↓reduceIte, Option.isSome_map]
        apply ih sourceParent sourceUnique targetUnique included
        change sourceParent.signature.infinitesimals + 1 ≤ parent.signature.infinitesimals + 1 at depth
        omega

/-- Reconciliation succeeds under the same key and depth conditions while
retaining the existing ordered inclusion whenever it is available. -/
theorem Chain.reconcile?_success {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign)
    (sourceUnique : source.signature.constants.Nodup)
    (targetUnique : target.signature.constants.Nodup)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (target.reconcile? source).isSome = true := by
  unfold Chain.reconcile?
  split
  · rfl
  · exact target.reorder?_success source sourceUnique targetUnique included depth

/-- An available ordered inclusion is returned without positional exchanges. -/
theorem Chain.reconcile?_ordered {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign)
    (map : FieldEmbedding K L) (accepted : target.subsequence? source = some map) :
    target.reconcile? source = some map := by
  simp only [Chain.reconcile?, accepted]

/-- A self inclusion keeps the original native identity map. -/
theorem Chain.reconcile?_self {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (chain : Chain registry K sign) :
    chain.reconcile? chain = some (FieldEmbedding.identity K) :=
  chain.reconcile?_ordered chain _ chain.subsequence?_self

/-- Reconcile the actual staged carriers retained by packed context handles. -/
@[expose] def PackedContext.reconcile? (source target : PackedContext registry) :
    Option (FieldEmbedding source.Carrier target.Carrier) := by
  cases source with
  | pack original =>
    cases target with
    | pack following => exact following.chain.reconcile? original.chain

/-- Packed reconciliation uses the original actual chain maps. -/
theorem PackedContext.reconcile?_ofChain
    {K L : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field L] [DecidableEq L] {sourceSign : K → Int} {targetSign : L → Int}
    (source : Chain registry K sourceSign) (target : Chain registry L targetSign) :
    (PackedContext.pack (Context.ofChain source)).reconcile?
      (.pack (Context.ofChain target)) = target.reconcile? source := by
  change (Context.ofChain target).chain.reconcile? (Context.ofChain source).chain = _
  rw [Context.ofChain_chain, Context.ofChain_chain]

/-- The packed factory produces a map whenever distinct provider keys are
included and the target retains sufficient infinitesimal depth. -/
theorem PackedContext.reconcile?_success (source target : PackedContext registry)
    (sourceUnique : source.signature.constants.Nodup)
    (targetUnique : target.signature.constants.Nodup)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (source.reconcile? target).isSome = true := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      exact target.chain.reconcile?_success source.chain sourceUnique targetUnique included depth

/-- Packed self reconciliation preserves the original native identity. -/
theorem PackedContext.reconcile?_self (context : PackedContext registry) :
    context.reconcile? context = some (FieldEmbedding.identity context.Carrier) := by
  cases context with
  | pack context => exact context.chain.reconcile?_self

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.Chain.reconcile?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.reconcile?_ordered

/-- info: 'Hex.RealClosure.BaseContext.Chain.reconcile?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.reconcile?_self

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.reconcile?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.reconcile?_self

/-- info: 'Hex.RealClosure.BaseContext.Chain.reorder?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.reorder?_success

/-- info: 'Hex.RealClosure.BaseContext.Chain.reconcile?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.reconcile?_success

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.reconcile?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.reconcile?_success
