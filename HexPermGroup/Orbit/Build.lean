/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit.Tree
public import HexPermGroup.Word.Build

public section

namespace Hex.PermGroup.Orbit.Tree

variable {n : Nat} {S : Array (Perm n)} {a : Fin n}

/-- Transporter roots for the first `k` discovery entries, sharing an append-only
program. Bounds and transporter invariants are erased during compilation. -/
structure Certificates (t : Tree S a) (k : Nat) where
  arena : Program.Builder S
  roots : Vector Nat k
  size : k ≤ t.points.size
  bound : ∀ j : Fin k, roots[j.val] < arena.values.size
  image : ∀ j : Fin k, (arena.values[roots[j.val]]'(bound j)).val.get a = t.points[j.val]
  identity : ∀ j : Fin k, t.points[j.val] = a →
    (arena.values[roots[j.val]]'(bound j)).val = Perm.id n

namespace Certificates

variable {t : Tree S a} {k : Nat}

@[expose] def empty (t : Tree S a) : Certificates t 0 where
  arena := .empty S
  roots := #v[]
  size := Nat.zero_le _
  bound := fun j => nomatch j
  image := fun j => nomatch j
  identity := fun j => nomatch j

/-- Retain earlier roots when the arena grows, then append one new transporter. -/
@[expose] def append (c : Certificates t k) (hk : k < t.points.size)
    (b : Program.Builder S) (hs : c.arena.values.size ≤ b.values.size)
    (he : ∀ j : Fin c.arena.values.size, b.values[j.val] = c.arena.values[j.val])
    (r : Fin b.values.size) (hi : b.values[r.val].val.get a = t.points[k])
    (hid : t.points[k] = a → b.values[r.val].val = Perm.id n) : Certificates t (k + 1) where
  arena := b
  roots := c.roots.push r.val
  size := hk
  bound := by
    intro ⟨j, hj⟩
    by_cases hlt : j < k
    · simpa [Vector.getElem_push_lt hlt] using Nat.lt_of_lt_of_le (c.bound ⟨j, hlt⟩) hs
    · have hjk : j = k := by omega
      subst j
      simp [r.isLt]
  image := by
    intro ⟨j, hj⟩
    by_cases hlt : j < k
    · simpa [Vector.getElem_push_lt hlt, he ⟨c.roots[j], c.bound ⟨j, hlt⟩⟩] using
        c.image ⟨j, hlt⟩
    · have hjk : j = k := by omega
      subst j
      simpa using hi
  identity := by
    intro ⟨j, hj⟩ h
    by_cases hlt : j < k
    · simpa [Vector.getElem_push_lt hlt, he ⟨c.roots[j], c.bound ⟨j, hlt⟩⟩] using
        c.identity ⟨j, hlt⟩ h
    · have hjk : j = k := by omega
      subst j
      simpa using hid h

/-- Compile one parent edge. The generator is composed on the left of its
parent's transporter, using earlier node references rather than copied words. -/
@[expose] def next (c : Certificates t k) (hk : k < t.points.size) : Certificates t (k + 1) :=
  match hp : t.parents[k] with
  | none =>
    c.append hk c.arena.id (by simp) c.arena.get_id
      ⟨c.arena.values.size, by simp⟩
      (by
        have hed := t.edge ⟨k, hk⟩
        simp only [hp] at hed
        simpa [c.arena.last_id] using hed.symm)
      (by intro _; exact c.arena.last_id)
  | some (j, i) =>
    have hed := t.edge ⟨k, hk⟩
    have hj : j < k := (show ∃ h : j < k, S[i.val].get t.points[j] = t.points[k] from
      by simpa only [hp] using hed).1
    let r : Fin c.arena.values.size := ⟨c.roots[j], c.bound ⟨j, hj⟩⟩
    c.append hk (c.arena.act i r) (by simp) (c.arena.get_act i r)
      ⟨c.arena.values.size + 1, by simp⟩
      (by
        rw [c.arena.last_act, Perm.get_comp]
        have him := c.image ⟨j, hj⟩
        simp only [r] at *
        rw [him]
        exact (show ∃ h : j < k, S[i.val].get t.points[j] = t.points[k] from
          by simpa only [hp] using hed).2)
      (by
        intro h
        have := t.base_parent ⟨k, hk⟩ h
        simp [hp] at this)

/-- Compile the remaining entries in discovery order. -/
@[expose] def finish {k : Nat} (c : Certificates t k) : Certificates t t.points.size :=
  if hk : k < t.points.size then
    finish (c.next hk)
  else cast (congrArg (Certificates t) (Nat.le_antisymm c.size (Nat.le_of_not_gt hk))) c
termination_by t.points.size - k

theorem next_size (c : Certificates t k) (hk : k < t.points.size) :
    (c.next hk).arena.values.size ≤ c.arena.values.size + 2 := by
  unfold next
  split <;> simp [append]

/-- Compiling a tree adds at most two nodes per point, regardless of path length. -/
theorem finish_size {k : Nat} (c : Certificates t k) :
    c.finish.arena.values.size ≤ c.arena.values.size + 2 * (t.points.size - k) := by
  rw [finish]
  split
  · rename_i hk
    have hr := finish_size (c.next hk)
    have hs := c.next_size hk
    omega
  · rename_i hk
    have he : k = t.points.size := Nat.le_antisymm c.size (Nat.le_of_not_gt hk)
    subst k
    simp
termination_by t.points.size - k

theorem nodes_le (t : Tree S a) :
    (empty t).finish.arena.nodes.size ≤ 2 * t.points.size := by
  rw [← Program.Builder.size_eq]
  simpa [empty, Program.Builder.empty] using finish_size (empty t)

/-- Convert natural lookup indices to bounded indices once, after discovery. -/
@[expose] def lookup (t : Tree S a) (x : Fin n) : Option (Fin t.points.size) :=
  match h : t.lookup[x.val] with
  | none => none
  | some j => some ⟨j, (t.point_lookup x j h).1⟩

theorem lookup_point (t : Tree S a) (j : Fin t.points.size) :
    lookup t t.points[j.val] = some j := by
  unfold lookup
  split
  · rename_i h
    have he := Tree.lookup_point t j
    simp [h] at he
  · rename_i k h
    have he : k = j.val := Option.some.inj (h.symm.trans (Tree.lookup_point t j))
    simp [he]

theorem lookup_none (t : Tree S a) (x : Fin n) : lookup t x = none ↔ x ∉ t.points := by
  rw [← t.missing x]
  unfold lookup
  split <;> simp_all

theorem point_lookup (t : Tree S a) (x : Fin n) (j : Fin t.points.size)
    (h : lookup t x = some j) : t.points[j.val] = x := by
  unfold lookup at h
  split at h
  · simp at h
  · rename_i k hk
    have he : k = j.val := congrArg Fin.val (Option.some.inj h)
    simpa only [he] using (t.point_lookup x k hk).2

/-- All emitted words share the completed arena's node array. -/
@[expose] def orbit (c : Certificates t t.points.size) : Orbit n where
  points := t.points
  lookup := Hex.Vector.ofFn' (lookup t)
  reps := Hex.Vector.ofFn' fun j => (c.arena.values[c.roots[j.val]]'(c.bound j)).val
  words := Hex.Vector.ofFn' fun j => c.arena.program ⟨c.roots[j.val], c.bound j⟩

theorem valid (c : Certificates t t.points.size) (ht : t.Processed t.points.size)
    (hs : ∀ p ∈ S, p.inv ∈ S) : c.orbit.Valid S a := by
  refine ⟨t.nodup, t.base, ?_, ?_, ?_, ?_⟩
  · intro j
    simpa [orbit] using lookup_point t j
  · intro x
    constructor
    · simpa [orbit] using lookup_none t x
    · intro j hj
      exact point_lookup t x j (by simpa [orbit] using hj)
  · intro j
    simp only [orbit, Hex.Vector.getElem_ofFn']
    exact ⟨c.arena.check_program _, c.image j, c.identity j⟩
  · intro i j
    refine ⟨ht j j.isLt i, ?_⟩
    obtain ⟨k, hk, he⟩ := Array.mem_iff_getElem.mp (hs S[i.val] (Array.getElem_mem i.isLt))
    simpa only [he, orbit] using ht j j.isLt ⟨k, hk⟩

end Certificates

end Hex.PermGroup.Orbit.Tree

namespace Hex.PermGroup.Orbit

/-- Construct a checked orbit for an inverse-closed generator array, retaining
its order and indices in the discovery edges and transporter programs. -/
@[expose] def ofSymmetric (S : Array (Perm n)) (a : Fin n)
    (hs : ∀ p ∈ S, p.inv ∈ S) : {c : Orbit n // c.Valid S a} :=
  let t := breadthFirst S a
  let c := (Tree.Certificates.empty t.val).finish
  ⟨c.orbit, c.valid t.property hs⟩

theorem ofSymmetric_checks (S : Array (Perm n)) (a : Fin n)
    (hs : ∀ p ∈ S, p.inv ∈ S) : checkOrbit S a (ofSymmetric S a hs).val = true :=
  decide_eq_true (ofSymmetric S a hs).property

end Hex.PermGroup.Orbit
