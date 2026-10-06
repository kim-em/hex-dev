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

/-- A checked map between actual native real-prefix carriers. -/
abbrev RealChain.Factory (registry : Registry) : Type 1 :=
  {K L : Type} → [Lean.Grind.Field K] → [DecidableEq K] →
    [Lean.Grind.Field L] → [DecidableEq L] →
    {sourceApprox : K → Rat → Bounds} → {sourceSign : K → Int} →
    {targetApprox : L → Rat → Bounds} → {targetSign : L → Int} →
    RealChain registry L targetApprox targetSign →
    RealChain registry K sourceApprox sourceSign → Option (FieldEmbedding K L)

/-- Lift a checked real-prefix factory through the same retained or additional
infinitesimal stages. Both ordered and reordered factories use this alignment. -/
@[expose] def Chain.lift? (mapReal : RealChain.Factory registry) {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    Option (FieldEmbedding K L) :=
  match target with
  | @Chain.real _ B field eq approx sign targetReal =>
    match source with
    | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
      mapReal targetReal sourceReal
    | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
      (none : Option (FieldEmbedding (RationalFn A) B))
  | @Chain.infinitesimal _ B field eq sign parent =>
    if source.signature.infinitesimals < parent.signature.infinitesimals + 1 then
      (parent.lift? mapReal source).map fun previous =>
        previous.comp (FieldEmbedding.constants B)
    else
      match source with
      | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
        (none : Option (FieldEmbedding A (RationalFn B)))
      | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
        (parent.lift? mapReal sourceParent).map FieldEmbedding.rationalFunctions


@[expose] def Chain.subsequence? {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    Option (FieldEmbedding K L) :=
  Chain.lift? (fun target source => target.subsequence? source) target source

/-- The shared staged lift retains the existing ordered execution equations. -/
theorem Chain.subsequence?.eq_lift {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    target.subsequence? source =
  match target with
  | @Chain.real _ B field eq approx sign targetReal =>
    match source with
    | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
      targetReal.subsequence? sourceReal
    | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
      (none : Option (FieldEmbedding (RationalFn A) B))
  | @Chain.infinitesimal _ B field eq sign parent =>
    if source.signature.infinitesimals < parent.signature.infinitesimals + 1 then
      (parent.subsequence? source).map fun previous =>
        previous.comp (FieldEmbedding.constants B)
    else
      match source with
      | @Chain.real _ A sourceField sourceEq sourceApprox sourceSign sourceReal =>
        (none : Option (FieldEmbedding A (RationalFn B)))
      | @Chain.infinitesimal _ A sourceField sourceEq sourceSign sourceParent =>
        (parent.subsequence? sourceParent).map FieldEmbedding.rationalFunctions := by
  rw [Chain.subsequence?, Chain.lift?.eq_def]
  rfl

/-- Staged inclusion succeeds exactly for a real-key subsequence and a target
with at least as many successive infinitesimals. -/
theorem Chain.subsequence?_isSome {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (target : Chain registry L targetSign) (source : Chain registry K sourceSign) :
    (target.subsequence? source).isSome = true ↔
      List.Sublist source.signature.constants target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  induction target generalizing K with
  | real targetReal =>
    cases source with
    | real sourceReal =>
      change (targetReal.subsequence? sourceReal).isSome = true ↔
        List.Sublist sourceReal.keys targetReal.keys ∧ 0 ≤ 0
      rw [and_iff_left (Nat.le_refl 0)]
      exact targetReal.subsequence?_isSome sourceReal
    | infinitesimal sourceParent =>
      change false = true ↔ List.Sublist sourceParent.signature.constants targetReal.keys ∧
        sourceParent.signature.infinitesimals + 1 ≤ 0
      simp only [Bool.false_eq_true]
      constructor
      · intro impossible; exact impossible.elim
      · rintro ⟨_, depth⟩; omega
  | infinitesimal parent ih =>
    by_cases deeper : source.signature.infinitesimals < parent.signature.infinitesimals + 1
    · rw [Chain.subsequence?.eq_lift]
      simp only [deeper, ↓reduceIte, Option.isSome_map]
      rw [ih]
      change (List.Sublist source.signature.constants parent.signature.constants ∧
        source.signature.infinitesimals ≤ parent.signature.infinitesimals) ↔
          (List.Sublist source.signature.constants parent.signature.constants ∧
            source.signature.infinitesimals ≤ parent.signature.infinitesimals + 1)
      constructor
      · rintro ⟨keys, depths⟩; exact ⟨keys, by omega⟩
      · rintro ⟨keys, depths⟩; exact ⟨keys, by omega⟩
    · cases source with
      | real sourceReal =>
        change ¬ 0 < parent.signature.infinitesimals + 1 at deeper
        omega
      | infinitesimal sourceParent =>
        rw [Chain.subsequence?.eq_lift]
        simp only [deeper, ↓reduceIte, Option.isSome_map]
        rw [ih]
        change (List.Sublist sourceParent.signature.constants parent.signature.constants ∧
          sourceParent.signature.infinitesimals ≤ parent.signature.infinitesimals) ↔
            (List.Sublist sourceParent.signature.constants parent.signature.constants ∧
              sourceParent.signature.infinitesimals + 1 ≤ parent.signature.infinitesimals + 1)
        rw [Nat.add_le_add_iff_right]

/-- A staged self inclusion retains all real and infinitesimal variables. -/
theorem Chain.subsequence?_self {K : Type}
    [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (chain : Chain registry K sign) :
    chain.subsequence? chain = some (FieldEmbedding.identity K) := by
  induction chain with
  | real parent => exact parent.subsequence?_self
  | infinitesimal parent ih =>
    have aligned : ¬ parent.infinitesimal.signature.infinitesimals <
        parent.signature.infinitesimals + 1 := Nat.lt_irrefl _
    rw [Chain.subsequence?.eq_lift]
    simp only [aligned, ↓reduceIte, ih, Option.map_some,
      FieldEmbedding.rationalFunctions_identity]

/-- Read a checked staged subsequence using the original packed contexts. -/
@[expose] def PackedContext.subsequence? (source target : PackedContext registry) :
    Option (FieldEmbedding source.Carrier target.Carrier) := by
  cases source with
  | pack original =>
    cases target with
    | pack following => exact following.chain.subsequence? original.chain

/-- The packed staged reader retains the exact signature compatibility check. -/
theorem PackedContext.subsequence?_isSome (source target : PackedContext registry) :
    (source.subsequence? target).isSome = true ↔
      List.Sublist source.signature.constants target.signature.constants ∧
        source.signature.infinitesimals ≤ target.signature.infinitesimals := by
  cases source with
  | pack original =>
    cases target with
    | pack following => exact following.chain.subsequence?_isSome original.chain

/-- Packing both actual chains preserves the native subsequence factory. -/
theorem PackedContext.subsequence?_ofChain
    {K L : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field L] [DecidableEq L] {sourceSign : K → Int} {targetSign : L → Int}
    (source : Chain registry K sourceSign) (target : Chain registry L targetSign) :
    (PackedContext.pack (Context.ofChain source)).subsequence?
      (.pack (Context.ofChain target)) = target.subsequence? source := by
  change (Context.ofChain target).chain.subsequence? (Context.ofChain source).chain = _
  rw [Context.ofChain_chain, Context.ofChain_chain]

/-- A nominal staged self inclusion retains every stored coefficient. -/
theorem PackedContext.subsequence?_self (context : PackedContext registry) :
    context.subsequence? context = some (FieldEmbedding.identity context.Carrier) := by
  cases context with
  | pack context => exact context.chain.subsequence?_self

/-- Adding one target infinitesimal extends the already checked subsequence
map by constants, retaining all source infinitesimal variables. -/
theorem PackedContext.subsequence?_next (source : PackedContext registry)
    {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
    (target : Context registry K sign)
    (deeper : source.signature.infinitesimals ≤ target.chain.signature.infinitesimals) :
    source.subsequence? (.pack target.infinitesimal) =
      (source.subsequence? (.pack target)).map fun previous =>
        previous.comp (FieldEmbedding.constants K) := by
  cases source with
  | pack source =>
    change target.infinitesimal.chain.subsequence? source.chain =
      (target.chain.subsequence? source.chain).map _
    rw [Context.infinitesimal_chain, Chain.subsequence?.eq_lift]
    have depth : source.chain.signature.infinitesimals < target.chain.signature.infinitesimals + 1 :=
      Nat.lt_succ_of_le deeper
    simp only [depth, ↓reduceIte]

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

/-- info: 'Hex.RealClosure.BaseContext.Chain.subsequence?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.subsequence?_isSome

/-- info: 'Hex.RealClosure.BaseContext.Chain.subsequence?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Chain.subsequence?_self

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.subsequence?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.subsequence?_isSome

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.subsequence?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.subsequence?_self

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.subsequence?_next' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.subsequence?_next
