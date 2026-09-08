/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action

public section

namespace Hex.PermGroup.Action

variable {G : Group n} {α : Type u} [DecidableEq α] (a : Action G α)

/-- A recorded enumeration of an invariant domain. Closure is checked on the
signed original generators before any index permutation is constructed. -/
@[expose] def Domain (objects : Array α) : Prop :=
  objects.toList.Nodup ∧ ∀ i : Fin G.generators.size, ∀ j : Fin objects.size,
    let p : Element G := ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩
    a.act p objects[j.val] ∈ objects ∧ a.act p.inv objects[j.val] ∈ objects

instance (objects : Array α) : Decidable (a.Domain objects) :=
  inferInstanceAs (Decidable (_ ∧ _))

namespace Domain

variable {a : Action G α} {objects : Array α} (h : a.Domain objects)

include h in
omit [DecidableEq α] in
theorem invariant (p : Element G) (x : α) : x ∈ objects ↔ a.act p x ∈ objects := by
  apply a.invariant (fun x => x ∈ objects) _ p x
  intro i x
  have hc : ∀ y ∈ objects,
      a.act ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩ y ∈ objects ∧
      a.act (Element.inv ⟨G.generators[i.val], .generator (Array.getElem_mem i.isLt)⟩) y ∈ objects := by
    intro y hy
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hy
    exact h.2 i ⟨j, hj⟩
  constructor
  · exact fun hx => (hc x hx).1
  · intro hx
    simpa using (hc _ hx).2

/-- Linear lookup uses decidable equality; no unchecked hash or ordering is used. -/
@[expose] def index (x : α) (hx : x ∈ objects) : Fin objects.size :=
  ⟨objects.findIdx (fun y => decide (y = x)),
    Array.findIdx_lt_size_of_exists ⟨x, hx, by simp⟩⟩

@[simp] theorem object_index (x : α) (hx : x ∈ objects) :
    objects[(index x hx).val] = x := by
  exact of_decide_eq_true (Array.findIdx_getElem
    (p := fun y => decide (y = x))
    (w := Array.findIdx_lt_size_of_exists ⟨x, hx, by simp⟩))

include h in
omit [DecidableEq α] in
theorem object_injective {i j : Fin objects.size} (he : objects[i.val] = objects[j.val]) : i = j := by
  apply Fin.ext
  exact h.1.getElem_inj.mp he

/-- The induced action on the recorded domain indices. -/
@[expose] def act (p : Element G) (i : Fin objects.size) : Fin objects.size :=
  index (a.act p objects[i.val]) ((h.invariant p _).mp (Array.getElem_mem i.isLt))

@[simp] theorem object_act (p : Element G) (i : Fin objects.size) :
    objects[(h.act p i).val] = a.act p objects[i.val] := object_index ..

@[simp] theorem act_id (i : Fin objects.size) : h.act (Element.id G) i = i := by
  apply h.object_injective
  simp

theorem act_comp (p q : Element G) (i : Fin objects.size) :
    h.act (p.comp q) i = h.act p (h.act q i) := by
  apply h.object_injective
  simp [Action.act_comp]

@[simp] theorem act_inv (p : Element G) (i : Fin objects.size) : h.act p (h.act p.inv i) = i := by
  apply h.object_injective
  simp

@[simp] theorem inv_act (p : Element G) (i : Fin objects.size) : h.act p.inv (h.act p i) = i := by
  apply h.object_injective
  simp

/-- Every group element induces an executable permutation of the domain. -/
@[expose] def perm (p : Element G) : Perm objects.size :=
  Perm.ofFn (h.act p)
    (fun i j he => by
      have hh := congrArg (h.act p.inv) he
      simpa using hh)
    (fun i => ⟨h.act p.inv i, h.act_inv p i⟩)

@[simp] theorem get_perm (p : Element G) (i : Fin objects.size) : (h.perm p).get i = h.act p i :=
  Perm.get_ofFn ..

@[simp] theorem perm_id : h.perm (Element.id G) = Perm.id objects.size := by
  apply Perm.ext
  intro i
  simp

theorem perm_comp (p q : Element G) : h.perm (p.comp q) = (h.perm p).comp (h.perm q) := by
  apply Perm.ext
  intro i
  simp [act_comp]

@[simp] theorem perm_inv (p : Element G) : h.perm p.inv = (h.perm p).inv := by
  apply Perm.ext
  intro i
  apply (h.perm p).get_inj
  simp

/-- Identity in the image means every recorded object is fixed. -/
theorem perm_eq_id (p : Element G) : h.perm p = Perm.id objects.size ↔
    ∀ x ∈ objects, a.act p x = x := by
  constructor
  · intro he x hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    have hv := congrArg (fun q : Perm objects.size => objects[(q.get ⟨i, hi⟩).val]) he
    simpa using hv
  · intro hf
    apply Perm.ext
    intro i
    apply h.object_injective
    simpa using hf objects[i.val] (Array.getElem_mem i.isLt)

end Domain

end Hex.PermGroup.Action
