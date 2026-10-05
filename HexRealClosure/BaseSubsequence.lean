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
open scoped List

variable {registry : Registry}

/-- Embed a real chain whose registered keys occur in predecessor order in
the target. Matching keys retain their formal variable; omitted target keys
are added by constant inclusion. The target supplies its own progress proofs. -/
@[expose] def RealChain.subsequence? {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → Bounds} {targetSign : L → Int}
    (target : RealChain registry L targetApprox targetSign)
    (source : RealChain registry K sourceApprox sourceSign) :
    Option (FieldEmbedding K L) :=
  match target with
  | .base =>
    match source with
    | .base => some (FieldEmbedding.identity Rat)
    | @RealChain.step _ A field eq approx sign parent key bounds registered sp ap =>
      (none : Option (FieldEmbedding (RationalFn A) Rat))
  | @RealChain.step _ B field eq approx sign parent key bounds registered sp ap =>
    match source with
    | .base => (parent.subsequence? (RealChain.base (registry := registry))).map fun previous =>
        previous.comp (FieldEmbedding.constants B)
    | @RealChain.step _ A sourceField sourceEq sourceApprox sourceSign
        sourceParent sourceKey sourceBounds sourceRegistered sourceSp sourceAp =>
      if sourceKey = key then
        (parent.subsequence? sourceParent).map FieldEmbedding.rationalFunctions
      else
        (parent.subsequence?
          (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp)).map fun previous =>
          previous.comp (FieldEmbedding.constants B)

private theorem sublist_snoc {A : Type} (source target : List A) (old new : A)
    (different : old ≠ new) :
    List.Sublist (source ++ [old]) (target ++ [new]) ↔ List.Sublist (source ++ [old]) target := by
  have reversed : List.Sublist (source ++ [old]) target ↔
      List.Sublist (old :: source.reverse) target.reverse := by
    rw [← List.reverse_sublist, List.reverse_append]
    rfl
  rw [← List.reverse_sublist, List.reverse_append, List.reverse_append]
  simp only [List.reverse_singleton, List.singleton_append]
  constructor
  · intro included
    cases included with
    | cons _ previous => exact reversed.mpr previous
    | cons_cons _ previous => exact False.elim (different rfl)
  · intro included
    exact (reversed.mp included).cons new

/-- The checked native map exists exactly when the source keys are a
subsequence of the target keys. No progress premises are reconstructed. -/
theorem RealChain.subsequence?_isSome {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceApprox : K → Rat → Bounds} {sourceSign : K → Int}
    {targetApprox : L → Rat → Bounds} {targetSign : L → Int}
    (target : RealChain registry L targetApprox targetSign)
    (source : RealChain registry K sourceApprox sourceSign) :
    (target.subsequence? source).isSome = true ↔ List.Sublist source.keys target.keys := by
  induction target generalizing K with
  | base =>
    cases source with
    | base =>
      change true = true ↔ List.Sublist [] []
      exact iff_of_true rfl (.refl [])
    | step parent key bounds registered sp ap =>
      change false = true ↔ List.Sublist (parent.keys ++ [key]) []
      simp only [Bool.false_eq_true, List.sublist_nil, List.append_eq_nil_iff,
        List.cons_ne_nil, and_false]
  | step parent key bounds registered sp ap ih =>
    cases source with
    | base =>
      change ((parent.subsequence? RealChain.base).map
        (fun previous => previous.comp (FieldEmbedding.constants _))).isSome = true ↔
          List.Sublist [] (parent.keys ++ [key])
      rw [Option.isSome_map, ih]
      exact iff_of_true (List.nil_sublist _) (List.nil_sublist _)
    | step sourceParent sourceKey sourceBounds sourceRegistered sourceSp sourceAp =>
      by_cases same : sourceKey = key
      · subst sourceKey
        rw [RealChain.subsequence?]
        simp only [↓reduceIte, Option.isSome_map]
        change (parent.subsequence? sourceParent).isSome = true ↔
          List.Sublist (sourceParent.keys ++ [key]) (parent.keys ++ [key])
        rw [List.append_sublist_append_right]
        exact ih sourceParent
      · rw [RealChain.subsequence?]
        simp only [same, ↓reduceIte, Option.isSome_map]
        change (parent.subsequence?
          (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp)).isSome = true ↔
            List.Sublist (sourceParent.keys ++ [sourceKey]) (parent.keys ++ [key])
        exact (ih (sourceParent.step sourceKey sourceBounds sourceRegistered sourceSp sourceAp)).trans
          (sublist_snoc sourceParent.keys parent.keys sourceKey key same).symm

/-- Check inclusion between packed immutable real contexts while retaining
their actual coefficient dictionaries. -/
@[expose] def RealPrefix.subsequence? (source target : RealPrefix registry) :
    Option (FieldEmbedding source.Carrier target.Carrier) := by
  cases source with
  | pack original =>
    cases target with
    | pack following => exact following.chain.subsequence? original.chain

/-- The source and target retain the same formal variables on a self map. -/
theorem RealChain.subsequence?_self {K : Type}
    [Lean.Grind.Field K] [DecidableEq K]
    {approx : K → Rat → Bounds} {sign : K → Int}
    (chain : RealChain registry K approx sign) :
    chain.subsequence? chain = some (FieldEmbedding.identity K) := by
  induction chain with
  | base => rfl
  | step parent key bounds registered sp ap ih =>
    rw [RealChain.subsequence?]
    simp only [↓reduceIte, ih, Option.map_some, FieldEmbedding.rationalFunctions_identity]

/-- The packed reader checks the complete ordered key subsequence. -/
theorem RealPrefix.subsequence?_isSome (source target : RealPrefix registry) :
    (source.subsequence? target).isSome = true ↔ List.Sublist source.keys target.keys := by
  cases source with
  | pack original =>
    cases target with
    | pack following => exact following.chain.subsequence?_isSome original.chain

end Hex.RealClosure.BaseContext


/-- info: 'Hex.RealClosure.BaseContext.RealChain.subsequence?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.subsequence?_isSome

/-- info: 'Hex.RealClosure.BaseContext.RealPrefix.subsequence?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealPrefix.subsequence?_isSome

/-- info: 'Hex.RealClosure.BaseContext.RealChain.subsequence?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealChain.subsequence?_self
