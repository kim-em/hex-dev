/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Domain

public section

namespace Hex.PermGroup.Action

/-- An action orbit certificate retains transporters and their programs in the
original permutation generators. The objects need not have a faithful action. -/
structure Orbit (G : Group n) (α : Type u) where
  objects : Array α
  reps : Vector (Element G) objects.size
  words : Vector Program objects.size

namespace Orbit

variable {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α}

/-- Reachability, identity at the base, and closure under signed generators.
Only a complete certificate can justify a negative transporter answer. -/
@[expose] def Valid (a : Action G α) (x : α) (c : Orbit G α) : Prop :=
  a.Domain c.objects ∧ x ∈ c.objects ∧ ∀ i : Fin c.objects.size,
    checkWord G.generators c.reps[i.val].val c.words[i.val] = true ∧
    a.act c.reps[i.val] x = c.objects[i.val] ∧
    (c.objects[i.val] = x → c.reps[i.val] = Element.id G)

instance (a : Action G α) (x : α) (c : Orbit G α) : Decidable (c.Valid a x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

variable {c : Orbit G α} (h : c.Valid a x)

include h in
omit [DecidableEq α] in
theorem mem_iff (y : α) : y ∈ c.objects ↔ ∃ p : Element G, a.act p x = y := by
  constructor
  · intro hy
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
    exact ⟨c.reps[i], (h.2.2 ⟨i, hi⟩).2.1⟩
  · rintro ⟨p, rfl⟩
    exact (h.1.invariant p x).mp h.2.1

include h in
omit [DecidableEq α] in
@[simp] theorem rep_apply (i : Fin c.objects.size) : a.act c.reps[i.val] x = c.objects[i.val] :=
  (h.2.2 i).2.1

/-- Read the stored representative only after establishing domain membership. -/
@[expose] def transporter? (_valid : c.Valid a x) (y : α) : Option (Element G) :=
  if hy : y ∈ c.objects then some c.reps[(Domain.index y hy).val] else none

include h in
theorem transporter_isSome (y : α) : (transporter? h y).isSome = true ↔
    ∃ p : Element G, a.act p x = y := by
  rw [← mem_iff h]
  unfold transporter?
  split <;> simp_all

theorem transporter_sound (y : α) (p : Element G) (hp : transporter? h y = some p) :
    a.act p x = y := by
  unfold transporter? at hp
  split at hp
  · cases Option.some.inj hp
    rw [rep_apply h, Domain.object_index]
  · cases hp

end Orbit

/-- Replay reachability programs and signed generator closure on action objects. -/
@[expose] def checkOrbit {G : Group n} {α : Type u} [DecidableEq α]
    (a : Action G α) (x : α) (c : Orbit G α) : Bool := decide (c.Valid a x)

theorem checkOrbit_sound {G : Group n} {α : Type u} [DecidableEq α]
    {a : Action G α} {x : α} {c : Orbit G α} (h : checkOrbit a x c = true) (y : α) :
    y ∈ c.objects ↔ ∃ p : Element G, a.act p x = y :=
  Orbit.mem_iff (of_decide_eq_true h) y

end Hex.PermGroup.Action
