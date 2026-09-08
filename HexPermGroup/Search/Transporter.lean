/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Node

public section

namespace Hex.PermGroup.Search

/-- A simultaneous point transporter and the full stabilizer of all points
already assigned. The extending permutations form its represented coset. -/
structure Transporter (H : Group n) (target : Perm n) (points : List (Fin n)) where
  rep : Element H
  agrees : ∀ x ∈ points, rep.val.get x = target.get x
  group : Group n
  stabilizer : ∀ q : Perm n, Generated group.generators q ↔
    Generated H.generators q ∧ ∀ x ∈ points, q.get x = x

namespace Transporter

variable {H : Group n} {target : Perm n} {points : List (Fin n)}

/-- The maintained coset contains exactly the permutations extending the
assigned images, including all simultaneous constraints. -/
theorem contains_iff (t : Transporter H target points) (q : Perm n) :
    Generated t.group.generators (t.rep.val.inv.comp q) ↔
      Generated H.generators q ∧ ∀ x ∈ points, q.get x = target.get x := by
  rw [t.stabilizer]
  constructor
  · rintro ⟨hq, hf⟩
    refine ⟨?_, ?_⟩
    · simpa only [← Perm.comp_assoc, Perm.comp_inv_self, Perm.id_comp] using t.rep.property.comp hq
    · intro x hx
      have he := congrArg t.rep.val.get (hf x hx)
      simpa only [Perm.get_comp, Perm.get_inv_get, t.agrees x hx] using he
  · rintro ⟨hq, hf⟩
    refine ⟨t.rep.property.inv.comp hq, ?_⟩
    intro x hx
    simp only [Perm.get_comp, hf x hx, ← t.agrees x hx, Perm.inv_get_get]

@[expose] def empty (H : Group n) (target : Perm n) : Transporter H target [] where
  rep := Element.id H
  agrees := by simp
  group := H
  stabilizer := by simp

/-- Extend one point using a transporter in the current full point stabilizer,
then replace that stabilizer by its stabilizer of the new source point. -/
@[expose] def extend (t : Transporter H target points) (x : Fin n) (k : Element t.group)
    (hk : k.val.get x = t.rep.val.inv.get (target.get x)) : Transporter H target (x :: points) where
  rep := t.rep.comp ⟨k.val, ((t.stabilizer k.val).mp k.property).1⟩
  agrees := by
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · simp only [Element.comp, Perm.get_comp, hk, Perm.get_inv_get]
    · simpa only [Element.comp, Perm.get_comp, ((t.stabilizer k.val).mp k.property).2 y hy] using t.agrees y hy
  group := t.group.stabilizer x
  stabilizer := by
    intro q
    rw [Group.mem_stabilizer, t.stabilizer]
    simp only [List.forall_mem_cons]
    exact ⟨fun h => ⟨h.1.1, h.2, h.1.2⟩, fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩⟩

theorem cannot_extend (t : Transporter H target points) (x : Fin n)
    (h : t.group.transporter? x (t.rep.val.inv.get (target.get x)) = none) :
    ¬ ∃ q : Element H, ∀ y ∈ x :: points, q.val.get y = target.get y := by
  rintro ⟨q, hq⟩
  have hm : Generated t.group.generators (t.rep.val.inv.comp q.val) :=
    (t.contains_iff q.val).mpr ⟨q.property, fun y hy => hq y (List.mem_cons_of_mem x hy)⟩
  apply (t.group.transporter_none x _).mp h
  exact ⟨⟨t.rep.val.inv.comp q.val, hm⟩, by simp only [Perm.get_comp, hq x (List.mem_cons_self)]⟩

end Transporter

/-- Failure of simultaneous extension is justified by a failed orbit test,
not by a bound on the amount of search performed. -/
inductive TransportResult (H : Group n) (target : Perm n) (points : List (Fin n)) where
  | found (transporter : Transporter H target points)
  | impossible (proof : ¬ ∃ q : Element H, ∀ x ∈ points, q.val.get x = target.get x)

@[expose] def TransportResult.failed {H : Group n} {target : Perm n} {points : List (Fin n)} :
    TransportResult H target points → Bool
  | .found _ => false
  | .impossible _ => true

theorem TransportResult.failed_iff {H : Group n} {target : Perm n} {points : List (Fin n)}
    (r : TransportResult H target points) : r.failed = true ↔
      ¬ ∃ q : Element H, ∀ x ∈ points, q.val.get x = target.get x := by
  cases r with
  | found t =>
    constructor
    · intro h; cases h
    · intro h
      exact False.elim (h ⟨t.rep, t.agrees⟩)
  | impossible h => simp [failed, h]

/-- Build a transporter coset by successive point stabilizers. Points are
processed from the list's end, so callers storing prefixes in reverse order
extend them in natural source-point order. -/
@[expose] def transport (H : Group n) (target : Perm n) (points : List (Fin n)) :
    TransportResult H target points :=
  match points with
  | [] => .found (Transporter.empty H target)
  | x :: xs =>
    match transport H target xs with
    | .impossible h => .impossible (by
        rintro ⟨q, hq⟩
        exact h ⟨q, fun y hy => hq y (List.mem_cons_of_mem x hy)⟩)
    | .found t =>
      match hk : t.group.transporter? x (t.rep.val.inv.get (target.get x)) with
      | none => .impossible (t.cannot_extend x hk)
      | some k => .found (t.extend x k (t.group.transporter_image x _ k hk))

end Hex.PermGroup.Search
