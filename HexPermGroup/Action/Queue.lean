/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Step

public section

namespace Hex.PermGroup.Action

/-- A breadth-first queue with shared transporter programs. Each object is
reachable, but closure is deliberately absent until traversal completes. -/
structure Queue (a : Action G α) (x : α) where
  objects : Array α
  arena : Program.Builder G.generators
  roots : Vector Nat objects.size
  bound : ∀ i : Fin objects.size, roots[i.val] < arena.values.size
  nodup : objects.toList.Nodup
  base : x ∈ objects
  image : ∀ i : Fin objects.size, a.act (arena.values[roots[i.val]]'(bound i)) x = objects[i.val]
  identity : ∀ i : Fin objects.size, objects[i.val] = x →
    (arena.values[roots[i.val]]'(bound i)) = Element.id G
  nodes_le : arena.nodes.size ≤ 3 * objects.size

namespace Queue

variable {G : Group n} {α : Type u} {a : Action G α} {x : α}

@[expose] def root (a : Action G α) (x : α) : Queue a x where
  objects := #[x]
  arena := (Program.Builder.empty G.generators).id
  roots := #v[0]
  bound := by
    intro ⟨i, hi⟩
    have : i = 0 := by simpa using hi
    subst i
    simp
  nodup := by simp
  base := by simp
  image := by
    intro ⟨i, hi⟩
    have : i = 0 := by simpa using hi
    subst i
    exact a.act_id x
  identity := by
    intro ⟨i, hi⟩ _
    have : i = 0 := by simpa using hi
    subst i
    rfl
  nodes_le := by simp [Program.Builder.id, Program.Builder.empty, Program.Builder.push]

/-- Extend only after checking that this neighbor has not been discovered. -/
@[expose] def push (t : Queue a x) (i : Fin t.objects.size) (s : Step G)
    (hnew : a.act s.element t.objects[i.val] ∉ t.objects) : Queue a x where
  objects := t.objects.push (a.act s.element t.objects[i.val])
  arena := s.advance t.arena ⟨t.roots[i.val], t.bound i⟩
  roots := (t.roots.push ((s.advance t.arena ⟨t.roots[i.val], t.bound i⟩).values.size - 1)).cast (by simp)
  bound := by
    intro ⟨j, hj⟩
    by_cases hlt : j < t.objects.size
    · simpa [Vector.getElem_push_lt hlt] using
        Nat.lt_of_lt_of_le (t.bound ⟨j, hlt⟩) (s.advance_le t.arena ⟨t.roots[i.val], t.bound i⟩)
    · have he : j = t.objects.size := by simp at hj; omega
      subst j
      have hp := s.advance_pos t.arena ⟨t.roots[i.val], t.bound i⟩
      simp only [Vector.getElem_cast, Vector.getElem_push_eq]
      omega
  nodup := by
    simp only [Array.toList_push, List.nodup_append]
    refine ⟨t.nodup, by simp, ?_⟩
    simpa using (show ∀ y ∈ t.objects, y ≠ a.act s.element t.objects[i.val] from
      fun y hy he => hnew (he ▸ hy))
  base := Array.mem_push_of_mem _ t.base
  image := by
    intro ⟨j, hj⟩
    by_cases hlt : j < t.objects.size
    · simpa [Vector.getElem_push_lt hlt, Array.getElem_push_lt hlt,
        s.advance_get t.arena ⟨t.roots[i.val], t.bound i⟩ ⟨t.roots[j], t.bound ⟨j, hlt⟩⟩] using
        t.image ⟨j, hlt⟩
    · have he : j = t.objects.size := by simp at hj; omega
      subst j
      simpa only [Vector.getElem_cast, Vector.getElem_push_eq, Array.getElem_push_eq,
        s.advance_last, Action.act_comp] using congrArg (a.act s.element) (t.image i)
  identity := by
    intro ⟨j, hj⟩ he
    by_cases hlt : j < t.objects.size
    · have him : t.objects[j] = x := by simpa [Array.getElem_push_lt hlt] using he
      simpa [Vector.getElem_push_lt hlt,
        s.advance_get t.arena ⟨t.roots[i.val], t.bound i⟩ ⟨t.roots[j], t.bound ⟨j, hlt⟩⟩] using
        t.identity ⟨j, hlt⟩ him
    · have hjq : j = t.objects.size := by simp at hj; omega
      subst j
      simp only [Array.getElem_push_eq] at he
      exact False.elim (hnew (he.symm ▸ t.base))
  nodes_le := by
    rw [← Program.Builder.size_eq, Step.advance_size]
    have hb : t.arena.values.size ≤ 3 * t.objects.size := by
      simpa only [Program.Builder.size_eq] using t.nodes_le
    simp only [Array.size_push]
    split <;> omega

/-- Extension preserves discovery indices. -/
structure Extends (t u : Queue a x) : Prop where
  size : t.objects.size ≤ u.objects.size
  get : ∀ i : Fin t.objects.size, u.objects[i.val] = t.objects[i.val]

namespace Extends

theorem refl (t : Queue a x) : Extends t t := ⟨Nat.le_refl _, fun _ => rfl⟩

theorem trans {t u v : Queue a x} (htu : Extends t u) (huv : Extends u v) : Extends t v :=
  ⟨Nat.le_trans htu.size huv.size, fun i =>
    (huv.get ⟨i.val, Nat.lt_of_lt_of_le i.isLt htu.size⟩).trans (htu.get i)⟩

theorem mem {t u : Queue a x} (h : Extends t u) {y : α} (hy : y ∈ t.objects) : y ∈ u.objects := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
  rw [← h.get ⟨i, hi⟩]
  exact Array.getElem_mem _

end Extends

theorem push_extends (t : Queue a x) (i : Fin t.objects.size) (s : Step G)
    (hnew : a.act s.element t.objects[i.val] ∉ t.objects) : Extends t (t.push i s hnew) :=
  ⟨by simp [push], fun j => by simp [push, Array.getElem_push_lt j.isLt]⟩

/-- Export all transporter roots against their one shared node array. -/
@[expose] def orbit (t : Queue a x) : Orbit G α where
  objects := t.objects
  reps := Hex.Vector.ofFn' fun i => t.arena.values[t.roots[i.val]]'(t.bound i)
  words := Hex.Vector.ofFn' fun i => t.arena.program ⟨t.roots[i.val], t.bound i⟩

theorem orbit_nodes (t : Queue a x) (i : Fin t.objects.size) :
    (t.orbit.words[i.val]'(by simp [orbit])).nodes.size ≤ 3 * t.objects.size := by
  simpa [orbit, Program.Builder.program] using t.nodes_le

theorem reachable (t : Queue a x) (y : α) (hy : y ∈ t.objects) : ∃ p : Element G, a.act p x = y := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hy
  exact ⟨t.arena.values[t.roots[i]]'(t.bound ⟨i, hi⟩), t.image ⟨i, hi⟩⟩

/-- All signed edges from the first `cursor` entries have been inspected. -/
@[expose] def Processed (t : Queue a x) (cursor : Nat) : Prop :=
  ∀ i : Fin t.objects.size, i.val < cursor →
    ∀ s : Step G, a.act s.element t.objects[i.val] ∈ t.objects

theorem orbit_valid (t : Queue a x) (hc : t.Processed t.objects.size) : (t.orbit).Valid a x := by
  refine ⟨⟨t.nodup, ?_⟩, t.base, ?_⟩
  · intro i j
    exact ⟨hc j j.isLt (i, false), hc j j.isLt (i, true)⟩
  · intro i
    simp only [orbit, Hex.Vector.getElem_ofFn']
    exact ⟨t.arena.check_program _, t.image i, t.identity i⟩

end Queue

end Hex.PermGroup.Action
