/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BasePermutation
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
