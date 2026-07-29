/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std.Data.ExtTreeMap.Lemmas

@[expose] public section

/-!
Reusable operations missing from `Std.ExtTreeMap`.

The declarations stay in the `Std.ExtTreeMap` namespace and use only standard
library types so they can be proposed upstream independently of Hex.

`mergeWith?` is the deletion-capable analogue of `mergeWith`. It folds the
smaller tree into the larger one, preserving the argument order seen by the
collision function. `foldl₂` performs one ordered traversal of both maps and
reports left-only, shared, and right-only keys without repeated lookup.
-/

namespace Std.ExtTreeMap

universe u v w x

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
  {cmp : α → α → Ordering}

/-- Fold two sorted entry streams together.

At a shared key the left key is passed to `f`; `LawfulEqCmp` ensures that the
right key is propositionally equal to it. -/
def mergeFold [LawfulEqCmp cmp]
    (f : δ → α → Option β → Option γ → δ) :
    δ → List (α × β) → List (α × γ) → δ
  | acc, [], right =>
      right.foldl (fun acc entry => f acc entry.1 none (some entry.2)) acc
  | acc, left, [] =>
      left.foldl (fun acc entry => f acc entry.1 (some entry.2) none) acc
  | acc, leftEntry :: left, rightEntry :: right =>
      match cmp leftEntry.1 rightEntry.1 with
      | .lt =>
          mergeFold f
            (f acc leftEntry.1 (some leftEntry.2) none)
            left (rightEntry :: right)
      | .eq =>
          mergeFold f
            (f acc leftEntry.1 (some leftEntry.2) (some rightEntry.2))
            left right
      | .gt =>
          mergeFold f
            (f acc rightEntry.1 none (some rightEntry.2))
            (leftEntry :: left) right
termination_by _ left right => left.length + right.length
decreasing_by all_goals simp_wf <;> omega

/-- Joint ordered fold over two maps.

The callback sees `some` on the sides that contain the current key. The
implementation is linear in the combined entry count after materializing the
two ordered streams. -/
def foldl₂ [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtTreeMap α β cmp) (right : ExtTreeMap α γ cmp) : δ :=
  mergeFold (cmp := cmp) f init left.toList right.toList

/-- Result for one key in a deletion-capable merge. -/
def mergeValue? (f : α → β → β → Option β) (key : α) :
    Option β → Option β → Option β
  | none, right => right
  | left, none => left
  | some left, some right => f key left right

/-- Merge two maps, allowing a collision to delete its key.

Left-only and right-only entries are retained unchanged. The smaller map is
folded into the larger map, so the operation performs
`O(min(m,n) * log(max(m,n)))` tree work. The collision callback always receives
the left value before the right value, independent of which map is smaller. -/
def mergeWith? [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → Option β)
    (left right : ExtTreeMap α β cmp) : ExtTreeMap α β cmp :=
  if left.size < right.size then
    left.foldl
      (fun out key leftValue =>
        out.alter key (mergeValue? f key (some leftValue)))
      right
  else
    right.foldl
      (fun out key rightValue =>
        out.alter key fun leftValue =>
          mergeValue? f key leftValue (some rightValue))
      left

private theorem getElem?_foldl_alter_of_forall [TransCmp cmp]
    (entries : List (α × γ)) (out : ExtTreeMap α β cmp)
    (update : α → γ → Option β → Option β) (key : α)
    (h : ∀ entry ∈ entries, cmp entry.1 key ≠ .eq) :
    (entries.foldl
      (fun out entry => out.alter entry.1 (update entry.1 entry.2))
      out)[key]? = out[key]? := by
  induction entries generalizing out with
  | nil => rfl
  | cons entry entries ih =>
      rw [List.foldl_cons, ih]
      · rw [getElem?_alter, if_neg (h entry (by simp))]
      · intro later hlater
        exact h later (by simp [hlater])

private theorem getElem?_foldl_alter_of_mem
    [TransCmp cmp] [LawfulEqCmp cmp]
    (entries : List (α × γ)) (out : ExtTreeMap α β cmp)
    (update : α → γ → Option β → Option β) (key : α) (value : γ)
    (hpair : entries.Pairwise (fun a b => cmp a.1 b.1 ≠ .eq))
    (hmem : (key, value) ∈ entries) :
    (entries.foldl
      (fun out entry => out.alter entry.1 (update entry.1 entry.2))
      out)[key]? = update key value out[key]? := by
  induction entries generalizing out with
  | nil => simp at hmem
  | cons entry entries ih =>
      simp only [List.pairwise_cons] at hpair
      rcases List.mem_cons.mp hmem with heq | hmem
      · subst entry
        rw [List.foldl_cons,
          getElem?_foldl_alter_of_forall entries
            (out.alter key (update key value)) update key]
        · rw [getElem?_alter_self]
        · intro later hlater heq
          have hkey : later.1 = key := LawfulEqCmp.eq_of_compare heq
          apply hpair.1 later hlater
          simp [hkey]
      · rw [List.foldl_cons, ih (out := out.alter entry.1 (update entry.1 entry.2))
          hpair.2 hmem, getElem?_alter, if_neg (hpair.1 (key, value) hmem)]

private theorem getElem?_foldl_alter [TransCmp cmp] [LawfulEqCmp cmp]
    (source : ExtTreeMap α γ cmp) (out : ExtTreeMap α β cmp)
    (update : α → γ → Option β → Option β) (key : α) :
    (source.foldl (fun out key value => out.alter key (update key value)) out)[key]? =
      match source[key]? with
      | none => out[key]?
      | some value => update key value out[key]? := by
  rw [foldl_eq_foldl_toList]
  cases hsource : source[key]? with
  | none =>
      rw [getElem?_foldl_alter_of_forall]
      intro entry hentry heq
      have hkey : entry.1 = key := LawfulEqCmp.eq_of_compare heq
      have hentryGet : source[entry.1]? = some entry.2 :=
        mem_toList_iff_getElem?_eq_some.mp hentry
      rw [hkey, hsource] at hentryGet
      contradiction
  | some value =>
      rw [getElem?_foldl_alter_of_mem source.toList out update key value
        source.distinct_keys_toList
        (mem_toList_iff_getElem?_eq_some.mpr hsource)]

/-- Lookup specification for a deletion-capable merge. -/
@[simp] theorem getElem?_mergeWith? [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → Option β)
    (left right : ExtTreeMap α β cmp) (key : α) :
    (mergeWith? f left right)[key]? =
      mergeValue? f key left[key]? right[key]? := by
  unfold mergeWith?
  split
  · rw [getElem?_foldl_alter]
    cases left[key]? <;> cases right[key]? <;> rfl
  · rw [getElem?_foldl_alter]
    cases left[key]? <;> cases right[key]? <;> rfl

@[simp] theorem foldl₂_empty_left [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (right : ExtTreeMap α γ cmp) :
    foldl₂ f init (∅ : ExtTreeMap α β cmp) right =
      right.foldl (fun acc key value => f acc key none (some value)) init := by
  unfold foldl₂
  have hempty : (∅ : ExtTreeMap α β cmp).toList = [] :=
    toList_eq_nil_iff.mpr rfl
  rw [hempty, mergeFold, foldl_eq_foldl_toList]

@[simp] theorem foldl₂_empty_right [TransCmp cmp] [LawfulEqCmp cmp]
    (f : δ → α → Option β → Option γ → δ) (init : δ)
    (left : ExtTreeMap α β cmp) :
    foldl₂ f init left (∅ : ExtTreeMap α γ cmp) =
      left.foldl (fun acc key value => f acc key (some value) none) init := by
  unfold foldl₂
  have hempty : (∅ : ExtTreeMap α γ cmp).toList = [] :=
    toList_eq_nil_iff.mpr rfl
  rw [hempty, foldl_eq_foldl_toList]
  cases hleft : left.toList <;> simp [mergeFold]

@[simp] theorem mergeWith?_empty_left [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → Option β) (right : ExtTreeMap α β cmp) :
    mergeWith? f ∅ right = right := by
  unfold mergeWith?
  rw [size_empty]
  split
  · rw [foldl_eq_foldl_toList]
    have hempty : (∅ : ExtTreeMap α β cmp).toList = [] :=
      toList_eq_nil_iff.mpr rfl
    rw [hempty]
    rfl
  · rename_i hsize
    have hright : right = ∅ := eq_empty_iff_size_eq_zero.mpr (by omega)
    subst right
    rw [foldl_eq_foldl_toList]
    have hempty : (∅ : ExtTreeMap α β cmp).toList = [] :=
      toList_eq_nil_iff.mpr rfl
    rw [hempty]
    rfl

@[simp] theorem mergeWith?_empty_right [TransCmp cmp] [LawfulEqCmp cmp]
    (f : α → β → β → Option β) (left : ExtTreeMap α β cmp) :
    mergeWith? f left ∅ = left := by
  simp only [mergeWith?, size_empty, Nat.not_lt_zero, ↓reduceIte]
  rw [foldl_eq_foldl_toList]
  have hempty : (∅ : ExtTreeMap α β cmp).toList = [] :=
    toList_eq_nil_iff.mpr rfl
  rw [hempty]
  rfl

end Std.ExtTreeMap
