/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Domain

public section

namespace Hex.PermGroup

/-- A partition of all declared points. Each point is labelled by the least
point in its block; block order is therefore not additional structure. -/
structure Partition (n : Nat) where
  labels : Vector (Fin n) n
  least : ∀ i : Fin n, labels[i.val] ≤ i
  idem : ∀ i : Fin n, labels[labels[i.val].val] = labels[i.val]

namespace Partition

@[expose] def Same (p : Partition n) (x y : Fin n) : Prop := p.labels[x.val] = p.labels[y.val]

instance (p : Partition n) (x y : Fin n) : Decidable (p.Same x y) :=
  inferInstanceAs (Decidable (_ = _))

theorem ext_labels {p q : Partition n} (h : p.labels = q.labels) : p = q := by
  cases p; cases q; cases h; rfl

instance : DecidableEq (Partition n) := fun p q =>
  if h : p.labels = q.labels then .isTrue (ext_labels h)
  else .isFalse fun he => h (congrArg Partition.labels he)

/-- A canonical partition is determined solely by which pairs share a block. -/
@[ext] theorem ext {p q : Partition n} (h : ∀ x y, p.Same x y ↔ q.Same x y) : p = q := by
  apply ext_labels
  apply Vector.ext
  intro i hi
  apply Fin.le_antisymm
  · have he := (h ⟨i, hi⟩ q.labels[i]).mpr (q.idem ⟨i, hi⟩).symm
    exact he ▸ p.least q.labels[i]
  · have he := (h ⟨i, hi⟩ p.labels[i]).mp (p.idem ⟨i, hi⟩).symm
    exact he ▸ q.least p.labels[i]

section Normalize

variable {α : Type u} [DecidableEq α] (values : Vector α n)

/-- Find the least occurrence of the input label at a point. -/
@[expose] def label (x : Fin n) : Fin n :=
  Fin.cast (by simp) (Action.Domain.index (objects := values.toArray) values[x.val]
    (by simp))

@[simp] theorem value_label (x : Fin n) : values[(label values x).val] = values[x.val] := by
  exact Action.Domain.object_index (objects := values.toArray) values[x.val] (by simp)

theorem label_le (x : Fin n) : label values x ≤ x := by
  change values.toArray.findIdx (fun y => decide (y = values[x.val])) ≤ x.val
  by_cases h : values.toArray.findIdx (fun y => decide (y = values[x.val])) ≤ x.val
  · exact h
  · have he := Array.not_of_lt_findIdx (Nat.lt_of_not_ge h)
    simp at he

theorem label_eq {x y : Fin n} (h : values[x.val] = values[y.val]) : label values x = label values y := by
  apply Fin.ext
  simp [label, Action.Domain.index, h]

/-- Canonicalize arbitrary block labels without enumerating any partitions. -/
@[expose] def ofValues : Partition n where
  labels := Hex.Vector.ofFn' (label values)
  least x := by simpa using label_le values x
  idem x := by
    simp only [Hex.Vector.getElem_ofFn']
    exact label_eq values (value_label values x)

theorem ofValues_same (x y : Fin n) : (ofValues values).Same x y ↔ values[x.val] = values[y.val] := by
  simp only [Same, ofValues, Hex.Vector.getElem_ofFn']
  constructor
  · intro h
    have he := congrArg (fun i : Fin n => values[i.val]) h
    simpa using he
  · exact label_eq values

end Normalize

@[simp] theorem ofValues_labels (p : Partition n) : ofValues p.labels = p := by
  apply ext
  intro x y
  exact ofValues_same p.labels x y

/-- Canonical labels must name their own block's least member. This rejects
noncanonical arrays rather than treating arbitrary numeric labels as canonical. -/
@[expose] def ofLabels? (labels : Vector (Fin n) n) : Option (Partition n) :=
  if h : (∀ i : Fin n, labels[i.val] ≤ i) ∧
      ∀ i : Fin n, labels[labels[i.val].val] = labels[i.val] then
    some ⟨labels, h.1, h.2⟩
  else none

theorem ofLabels?_isSome (labels : Vector (Fin n) n) :
    (ofLabels? labels).isSome = true ↔
      (∀ i : Fin n, labels[i.val] ≤ i) ∧ ∀ i : Fin n, labels[labels[i.val].val] = labels[i.val] := by
  unfold ofLabels?
  split <;> simp_all

/-- Move the points of every block, then assign the new least-member labels.
The blocks themselves form an unordered family. -/
@[expose] def permute (s : Perm n) (p : Partition n) : Partition n :=
  ofValues (Hex.Vector.ofFn' fun x => p.labels[(s.inv.get x).val])

theorem permute_same (s : Perm n) (p : Partition n) (x y : Fin n) :
    (p.permute s).Same x y ↔ p.Same (s.inv.get x) (s.inv.get y) := by
  simp only [permute, ofValues_same, Hex.Vector.getElem_ofFn']
  rfl

@[simp] theorem permute_id (p : Partition n) : p.permute (Perm.id n) = p := by
  apply ext
  intro x y
  simp [permute_same]

theorem permute_comp (s t : Perm n) (p : Partition n) :
    p.permute (s.comp t) = (p.permute t).permute s := by
  apply ext
  intro x y
  simp [permute_same, Perm.inv_comp]

end Partition

namespace Action

@[expose] def partitions (G : Group n) : Action G (Partition n) where
  act p x := x.permute p.val
  id_act := Partition.permute_id
  comp_act p q x := Partition.permute_comp p.val q.val x

end Action

end Hex.PermGroup
