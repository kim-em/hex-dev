/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Action.Queue

public section

namespace Hex.PermGroup.Action

/-- A full discovery queue and proof that another reachable object exists.
Exhaustion supplies positive information only, with no coverage claim. -/
structure Exhausted (a : Action G α) (x : α) (cap : Nat) where
  queue : Queue a x
  full : queue.objects.size = cap
  more : ∃ y : α, (∃ p : Element G, a.act p x = y) ∧ y ∉ queue.objects

namespace Queue

variable {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α}

@[expose] def visit (cap : Nat) (t : Queue a x) (ht : t.objects.size ≤ cap)
    (i : Fin t.objects.size) (s : Step G) : Except (Exhausted a x cap)
      {u : Queue a x // Extends t u ∧ a.act s.element t.objects[i.val] ∈ u.objects ∧ u.objects.size ≤ cap} :=
  if hm : a.act s.element t.objects[i.val] ∈ t.objects then
    .ok ⟨t, .refl t, hm, ht⟩
  else if hc : t.objects.size < cap then
    .ok ⟨t.push i s hm, t.push_extends i s hm, by simp [push], by simp [push]; omega⟩
  else .error ⟨t, by omega, by
    obtain ⟨p, hp⟩ := t.reachable t.objects[i.val] (Array.getElem_mem i.isLt)
    exact ⟨a.act s.element t.objects[i.val], ⟨s.element.comp p, by rw [Action.act_comp, hp]⟩, hm⟩⟩

/-- Visit signed generators in their fixed input order. An exhausted traversal
retains the last full queue, including discoveries made earlier in this scan. -/
@[expose] def scan (cap : Nat) (t : Queue a x) (ht : t.objects.size ≤ cap)
    (i : Fin t.objects.size) (steps : List (Step G)) : Except (Exhausted a x cap)
      {u : Queue a x // Extends t u ∧
        (∀ s ∈ steps, a.act s.element t.objects[i.val] ∈ u.objects) ∧ u.objects.size ≤ cap} :=
  match steps with
  | [] => .ok ⟨t, .refl t, by simp, ht⟩
  | s :: steps =>
    match visit cap t ht i s with
    | .error e => .error e
    | .ok ⟨u, he, hm, hu⟩ =>
      match scan cap u hu ⟨i.val, Nat.lt_of_lt_of_le i.isLt he.size⟩ steps with
      | .error e => .error e
      | .ok ⟨v, hev, hv, hcap⟩ => .ok ⟨v, he.trans hev, by
          intro g hg
          rcases List.mem_cons.mp hg with hg | hg
          · subst g
            exact hev.mem hm
          · simpa only [he.get i] using hv g hg, hcap⟩

omit [DecidableEq α] in
theorem scan_processed {t u : Queue a x} (cursor : Nat) (hc : cursor < t.objects.size)
    (hp : t.Processed cursor) (he : Extends t u)
    (hs : ∀ s ∈ Step.all G, a.act s.element t.objects[cursor] ∈ u.objects) :
    u.Processed (cursor + 1) := by
  intro i hi s
  have hlt : i.val < t.objects.size := by omega
  rw [he.get ⟨i.val, hlt⟩]
  by_cases heq : i.val = cursor
  · simpa only [heq] using hs s (Step.mem_all s)
  · exact he.mem (hp ⟨i.val, hlt⟩ (by change i.val < cursor; omega) s)

/-- The cursor advances once for each discovered object. The checked object cap
is the termination bound; it does not require allocating an ambient domain. -/
@[expose] def finish (cap : Nat) (t : Queue a x) (ht : t.objects.size ≤ cap)
    (cursor : Nat) (hp : t.Processed cursor) : Except (Exhausted a x cap)
      {c : Orbit G α // c.Valid a x ∧ c.objects.size ≤ cap ∧
        ∀ i : Fin c.objects.size, c.words[i.val].nodes.size ≤ 3 * cap} :=
  if hc : cursor < t.objects.size then
    match scan cap t ht ⟨cursor, hc⟩ (Step.all G) with
    | .error e => .error e
    | .ok ⟨u, he, hs, hu⟩ =>
      finish cap u hu (cursor + 1) (scan_processed cursor hc hp he hs)
  else .ok ⟨t.orbit, t.orbit_valid (by
      intro i _ s
      exact hp i (by have := i.isLt; omega) s), ht,
      fun i => Nat.le_trans (t.orbit_nodes i) (Nat.mul_le_mul_left 3 ht)⟩
termination_by cap - cursor

end Queue

/-- Insufficient object capacity, including the inability to store the base. -/
inductive OrbitLimit (a : Action G α) (x : α) (cap : Nat) where
  | zero (empty : cap = 0)
  | full (exhausted : Exhausted a x cap)

/-- Deterministic BFS on just the requested orbit, retaining checked words in
the original generators. It never enumerates all tuples, subsets or partitions. -/
@[expose] def breadthFirst {G : Group n} {α : Type u} [DecidableEq α]
    (a : Action G α) (x : α) (cap : Nat) : Except (OrbitLimit a x cap)
      {c : Orbit G α // c.Valid a x ∧ c.objects.size ≤ cap ∧
        ∀ i : Fin c.objects.size, c.words[i.val].nodes.size ≤ 3 * cap} :=
  if hc : 0 < cap then
    (Queue.finish cap (Queue.root a x) (by simp [Queue.root]; omega)
      0 (by intro i hi; omega)).mapError OrbitLimit.full
  else .error (.zero (by omega))

/-- Every invariant domain containing the base needs room for the full queue
and the additional reachable object witnessed by exhaustion. -/
theorem Exhausted.tooSmall_domain {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α} {cap : Nat}
    (e : Exhausted a x cap) (objects : Array α) (hd : a.Domain objects)
    (hx : x ∈ objects) : cap < objects.size := by
  obtain ⟨y, hy, hnew⟩ := e.more
  have hn : (e.queue.objects.push y).toList.Nodup := by
    simp only [Array.toList_push, List.nodup_append]
    refine ⟨e.queue.nodup, by simp, ?_⟩
    simpa using (show ∀ z ∈ e.queue.objects, z ≠ y from fun z hz he => hnew (he ▸ hz))
  have hs : (e.queue.objects.push y).toList ⊆ objects.toList := by
    intro z hz
    simp only [Array.mem_toList_iff, Array.mem_push] at hz ⊢
    rcases hz with hz | hz
    · exact by
        obtain ⟨p, hp⟩ := e.queue.reachable z hz
        exact hp ▸ (hd.invariant p x).mp hx
    · subst z
      exact by
        obtain ⟨p, hp⟩ := hy
        exact hp ▸ (hd.invariant p x).mp hx
  have hh := List.nodup_subset_length_le hn hs
  have hh' : cap + 1 ≤ objects.size := by simpa [e.full] using hh
  omega

theorem Exhausted.tooSmall {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α} {cap : Nat}
    (e : Exhausted a x cap) (c : Orbit G α) (hc : c.Valid a x) : cap < c.objects.size :=
  e.tooSmall_domain c.objects hc.1 hc.2.1

theorem OrbitLimit.tooSmall_domain {G : Group n} {α : Type u} [DecidableEq α]
    {a : Action G α} {x : α} {cap : Nat} (e : OrbitLimit a x cap)
    (objects : Array α) (hd : a.Domain objects) (hx : x ∈ objects) : cap < objects.size := by
  cases e with
  | zero he => rw [he]; exact Array.size_pos_of_mem hx
  | full e => exact e.tooSmall_domain objects hd hx

theorem OrbitLimit.tooSmall {G : Group n} {α : Type u} [DecidableEq α] {a : Action G α} {x : α} {cap : Nat}
    (e : OrbitLimit a x cap) (c : Orbit G α) (hc : c.Valid a x) : cap < c.objects.size := by
  cases e with
  | zero he => rw [he]; exact Array.size_pos_of_mem hc.2.1
  | full e => exact e.tooSmall c hc

/-- A sufficient object budget guarantees completion, without assuming that
the action is faithful or enumerating the ambient type. -/
theorem breadthFirst_complete {G : Group n} {α : Type u} [DecidableEq α]
    (a : Action G α) (x : α) (cap : Nat) (c : Orbit G α) (hc : c.Valid a x)
    (hs : c.objects.size ≤ cap) : ∃ result, a.breadthFirst x cap = .ok result := by
  cases he : a.breadthFirst x cap with
  | ok result => exact ⟨result, rfl⟩
  | error e => have := e.tooSmall c hc; omega

/-- An invariant finite domain bounds every orbit it contains. The traversal
still discovers only this orbit, without copying the rest of the domain. -/
@[expose] def orbitOfDomain {G : Group n} {α : Type u} [DecidableEq α]
    (a : Action G α) (objects : Array α) (hd : a.Domain objects) (x : α) (hx : x ∈ objects) :
    {c : Orbit G α // c.Valid a x ∧ c.objects.size ≤ objects.size ∧
      ∀ i : Fin c.objects.size, c.words[i.val].nodes.size ≤ 3 * objects.size} :=
  match a.breadthFirst x objects.size with
  | .ok result => result
  | .error e => False.elim (Nat.lt_irrefl _ (e.tooSmall_domain objects hd hx))

end Hex.PermGroup.Action
