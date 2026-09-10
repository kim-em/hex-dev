/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraph.Basic
public import HexPermGroup.Perm

public section

/-! Graph canonical labels and compatibility names for shared permutations. -/

namespace Hex.GraphIso

export Hex (Perm)

namespace Perm
export Hex.Perm (get get_toList get_ne get_inj get_surj ext_vec ext nodup_ofFn_toList complete_ofFn_toList ofFn get_ofFn ofVector? isSome_ofVector? vec_of_ofVector? id get_id comp get_comp scatterStep invVec scatter_unchanged scatter_get preimage preimage_get get_preimage preimage_inj nodup_toList inv get_inv get_inv_get inv_get_get comp_id id_comp comp_assoc comp_inv_self inv_comp_self inv_inv inv_id inv_comp mk vec nodup complete ofNatArray?)
end Perm

/-- A canonical-labelling result array in nauty's `canonlab` convention:
`l[i]` is the old vertex placed at new position `i`. The underlying data is
the same duplicate-free complete vertex array as `Perm`. The wrapper marks
the direction. -/
structure Label (n : Nat) where
  /-- The underlying bijection sending each new position to the old vertex
  placed there. -/
  perm : Perm n

namespace Label

variable {n : Nat}

instance : DecidableEq (Label n) := fun l m =>
  if h : l.perm = m.perm then
    .isTrue (by cases l; cases m; cases h; rfl)
  else
    .isFalse fun e => h (congrArg Label.perm e)

/-- The old vertex at new position `i`. -/
@[inline, expose] def get (l : Label n) (i : Fin n) : Fin n :=
  l.perm.get i

instance : GetElem (Label n) (Fin n) (Fin n) (fun _ _ => True) where
  getElem l i _ := l.get i

@[simp] theorem getElem_eq_get (l : Label n) (i : Fin n) : l[i] = l.get i := rfl

@[ext] theorem ext {l m : Label n} (h : ∀ i, l.get i = m.get i) : l = m := by
  cases l; cases m
  exact congrArg Label.mk (Perm.ext h)

/-- Checked construction from a vertex array. -/
@[expose] def ofVector? (v : Vector (Fin n) n) : Option (Label n) :=
  (Perm.ofVector? v).map Label.mk

/-- The identity labelling. -/
@[expose] protected def id (n : Nat) : Label n :=
  ⟨Perm.id n⟩

@[simp] theorem get_id (i : Fin n) : (Label.id n).get i = i :=
  Perm.get_id i

/-- Sequential composition: relabelling by `l` and then by `m` is
relabelling by `l.comp m`, with `(l.comp m).get i = l.get (m.get i)`. -/
@[expose] def comp (l m : Label n) : Label n :=
  ⟨l.perm.comp m.perm⟩

@[simp] theorem get_comp (l m : Label n) (i : Fin n) :
    (l.comp m).get i = l.get (m.get i) :=
  Perm.get_comp ..

/-- The forward permutation of a labelling: old vertex `v` moves to the new
position where `l` placed it. -/
@[expose] def toPerm (l : Label n) : Perm n :=
  l.perm.inv

@[simp] theorem get_toPerm_get (l : Label n) (i : Fin n) :
    l.get (l.toPerm.get i) = i :=
  Perm.get_inv_get ..

@[simp] theorem toPerm_get_get (l : Label n) (i : Fin n) :
    l.toPerm.get (l.get i) = i :=
  Perm.inv_get_get ..

/-- Checked construction from a raw array of vertex numbers: `none`
unless the array has length `n`, entries below `n`, and describes a
permutation. -/
@[expose] def ofArray? (n : Nat) (lab : Array Nat) : Option (Label n) :=
  if h : lab.size = n ∧ ∀ v ∈ lab, v < n then
    ofVector? ⟨lab.attach.map fun v =>
      (⟨v.val, h.2 v.val v.property⟩ : Fin n), by simp [h.1]⟩
  else
    none

theorem ofVector?_perm_vec {v : Vector (Fin n) n} {l : Label n}
    (h : Label.ofVector? v = some l) : l.perm.vec = v := by
  rw [Label.ofVector?, Perm.ofVector?] at h
  split at h
  · simp only [Option.map_some] at h
    injection h with h'
    rw [← h']
  · simp at h

theorem ofArray?_bounds {lab : Array Nat} {l : Label n}
    (h : ofArray? n lab = some l) :
    lab.size = n ∧ ∀ v ∈ lab, v < n := by
  rw [ofArray?] at h
  split at h
  · assumption
  · cases h

/-- A checked labelling reads back the raw array entrywise. -/
theorem ofArray?_get {lab : Array Nat} {l : Label n}
    (h : ofArray? n lab = some l) (i : Nat) (hi : i < n) :
    (l.get ⟨i, hi⟩).val = lab[i]! := by
  rw [ofArray?] at h
  split at h
  · next hwf =>
    have hvec := ofVector?_perm_vec h
    show (l.perm.get ⟨i, hi⟩).val = lab[i]!
    have hlen : i < l.perm.vec.toList.length := by simpa using hi
    have h2 : l.perm.get ⟨i, hi⟩ = l.perm.vec.toList[i]'hlen :=
      (Perm.get_toList l.perm ⟨i, hi⟩).symm
    have h1 : l.perm.vec.toList =
        (⟨lab.attach.map fun v =>
          (⟨v.val, hwf.2 v.val v.property⟩ : Fin n), by
            simp [hwf.1]⟩ : Vector (Fin n) n).toList :=
      congrArg Vector.toList hvec
    rw [h2, List.getElem_of_eq h1 hlen]
    have hasz : i < (lab.attach.map fun v =>
        (⟨v.val, hwf.2 v.val v.property⟩ : Fin n)).size := by
      rw [Array.size_map, Array.size_attach]
      omega
    show (((lab.attach.map fun v =>
      (⟨v.val, hwf.2 v.val v.property⟩ : Fin n))[i]'hasz)).val =
      lab[i]!
    rw [Array.getElem_map]
    show (lab.attach[i]'(by rw [Array.size_attach]; omega)).val =
      lab[i]!
    rw [Array.getElem_attach]
    exact (getElem!_pos lab i (by omega)).symm
  · cases h

end Label

end Hex.GraphIso

namespace Hex.Perm

open Hex.GraphIso

/-- The labelling of a forward permutation: new position `i` holds the old
vertex mapped to `i`. -/
@[expose] def toLabel (p : Perm n) : Label n :=
  ⟨p.inv⟩

@[simp] theorem get_toLabel (p : Perm n) (i : Fin n) :
    p.toLabel.get i = p.inv.get i := rfl

@[simp] theorem toLabel_toPerm (p : Perm n) : p.toLabel.toPerm = p := by
  rw [toLabel, Label.toPerm, inv_inv]

@[simp] theorem toPerm_toLabel (l : Label n) : l.toPerm.toLabel = l := by
  cases l
  rw [Label.toPerm, toLabel, inv_inv]

end Hex.Perm

namespace Hex.GraphIso.Perm
export Hex.Perm (toLabel get_toLabel toLabel_toPerm toPerm_toLabel)
end Hex.GraphIso.Perm
