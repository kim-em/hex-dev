/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Orbit

public section

namespace Hex.PermGroup.Orbit

/-- A discovery tree. Parent edges refer to earlier entries and retain the
generator's input index. Lookup entries use natural numbers during construction,
so appending a point does not traverse the lookup vector to cast indices. -/
structure Tree (S : Array (Perm n)) (a : Fin n) where
  points : Array (Fin n)
  lookup : Vector (Option Nat) n
  parents : Vector (Option (Nat × Fin S.size)) points.size
  nodup : points.toList.Nodup
  base : a ∈ points
  lookup_point : ∀ j : Fin points.size, lookup[points[j.val].val] = some j.val
  point_lookup : ∀ (x : Fin n) (j : Nat), lookup[x.val] = some j →
    ∃ h : j < points.size, points[j] = x
  edge : ∀ j : Fin points.size,
    match parents[j.val] with
    | none => points[j.val] = a
    | some (k, i) => ∃ h : k < j.val, S[i.val].get points[k] = points[j.val]

namespace Tree

variable {n : Nat} {S : Array (Perm n)} {a : Fin n}

/-- Start the queue with its root. -/
@[expose] def root (S : Array (Perm n)) (a : Fin n) : Tree S a where
  points := #[a]
  lookup := (Vector.replicate n none).set a.val (some 0)
  parents := #v[none]
  nodup := by simp
  base := by simp
  lookup_point := by
    intro ⟨j, hj⟩
    have : j = 0 := by simpa using hj
    subst j
    simp
  point_lookup := by
    intro x j h
    by_cases hx : x = a
    · subst x
      simp at h
      subst j
      exact ⟨by simp, by simp⟩
    · have hv : x.val ≠ a.val := fun h => hx (Fin.ext h)
      simp [Ne.symm hv] at h
  edge := by
    intro ⟨j, hj⟩
    have : j = 0 := by simpa using hj
    subst j
    simp

theorem missing (t : Tree S a) (x : Fin n) : t.lookup[x.val] = none ↔ x ∉ t.points := by
  constructor
  · intro h hx
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
    have := t.lookup_point ⟨j, hj⟩
    simp [h] at this
  · intro hx
    cases h : t.lookup[x.val] with
    | none => rfl
    | some j =>
      obtain ⟨hj, he⟩ := t.point_lookup x j h
      exact False.elim (hx (he ▸ Array.getElem_mem hj))

theorem size_le (t : Tree S a) : t.points.size ≤ n := by
  have h := List.nodup_subset_length_le t.nodup
    (l₂ := List.finRange n) (by intro x _; exact List.mem_finRange x)
  simpa using h

theorem size_pos (t : Tree S a) : 0 < t.points.size :=
  Array.size_pos_of_mem t.base

theorem point_zero (t : Tree S a) : t.points[0]'t.size_pos = a := by
  have hz := t.size_pos
  have h := t.edge ⟨0, t.size_pos⟩
  cases he : t.parents[0] with
  | none => simpa [he] using h
  | some pair =>
    simp only [he] at h
    obtain ⟨h, _⟩ := h
    omega

theorem base_parent (t : Tree S a) (j : Fin t.points.size) (hj : t.points[j.val] = a) :
    t.parents[j.val] = none := by
  have hzero := t.lookup_point ⟨0, t.size_pos⟩
  have h := t.lookup_point j
  simp only [hj] at h
  simp only [t.point_zero] at hzero
  have hjzero : j.val = 0 := Option.some.inj (h.symm.trans hzero)
  have hed := t.edge j
  cases hp : t.parents[j.val] with
  | none => rfl
  | some pair =>
    simp only [hp] at hed
    obtain ⟨h, _⟩ := hed
    omega

/-- Following parent edges gives a generated transporter, independently of any
program encoding used to export the discovery tree. -/
theorem reachable (t : Tree S a) (j : Fin t.points.size) :
    ∃ p : Perm n, Generated S p ∧ p.get a = t.points[j.val] := by
  obtain ⟨j, hj⟩ := j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    have hed := t.edge ⟨j, hj⟩
    cases hp : t.parents[j] with
    | none =>
      simp only [hp] at hed
      exact ⟨Perm.id n, .id, by simpa using hed.symm⟩
    | some pair =>
      obtain ⟨k, i⟩ := pair
      simp only [hp] at hed
      obtain ⟨hk, he⟩ := hed
      obtain ⟨p, hgen, him⟩ := ih k hk (Nat.lt_trans hk hj)
      exact ⟨S[i.val].comp p, .comp (.generator (Array.getElem_mem i.isLt)) hgen,
        by simp [him, he]⟩

/-- Append a previously unseen neighbor and its parent edge. -/
@[expose] def push (t : Tree S a) (j : Fin t.points.size) (i : Fin S.size)
    (hnew : S[i.val].get t.points[j.val] ∉ t.points) : Tree S a where
  points := t.points.push (S[i.val].get t.points[j.val])
  lookup := t.lookup.set (S[i.val].get t.points[j.val]).val (some t.points.size)
  parents := (t.parents.push (some (j.val, i))).cast (by simp)
  nodup := by
    simp only [Array.toList_push, List.nodup_append]
    refine ⟨t.nodup, by simp, ?_⟩
    simpa using (show ∀ x ∈ t.points, x ≠ S[i.val].get t.points[j.val] from
      fun x hx he => hnew (he ▸ hx))
  base := Array.mem_push_of_mem _ t.base
  lookup_point := by
    intro ⟨k, hk⟩
    by_cases hlt : k < t.points.size
    · have hne : t.points[k] ≠ S[i.val].get t.points[j.val] := by
        intro h; exact hnew (h ▸ Array.getElem_mem hlt)
      have hv := fun h => hne (Fin.ext h)
      simp [Array.getElem_push_lt hlt, Ne.symm hv,
        t.lookup_point ⟨k, hlt⟩]
    · have he : k = t.points.size := by simp at hk; omega
      subst k
      simp
  point_lookup := by
    intro x k h
    by_cases hx : x = S[i.val].get t.points[j.val]
    · subst x
      simp at h
      subst k
      exact ⟨by simp, by simp⟩
    · have hv := fun h => hx (Fin.ext h)
      simp only [Vector.getElem_set, ite_eq_right (Ne.symm hv)] at h
      obtain ⟨hk, he⟩ := t.point_lookup x k h
      exact ⟨by simp; omega, by simpa [Array.getElem_push_lt hk] using he⟩
  edge := by
    intro ⟨k, hk⟩
    by_cases hlt : k < t.points.size
    · simp only [Vector.getElem_cast, Vector.getElem_push_lt hlt,
        Array.getElem_push_lt hlt]
      have hed := t.edge ⟨k, hlt⟩
      cases hp : t.parents[k] with
      | none => simpa [hp] using hed
      | some pair =>
        obtain ⟨l, g⟩ := pair
        simp only [hp] at hed
        obtain ⟨hl, he⟩ := hed
        exact ⟨hl, by simpa [Array.getElem_push_lt (Nat.lt_trans hl hlt)] using he⟩
    · have he : k = t.points.size := by simp at hk; omega
      subst k
      simp [Array.getElem_push_lt j.isLt, j.isLt]

/-- Extension preserves queue indices as well as membership. -/
structure Extends (t u : Tree S a) : Prop where
  size : t.points.size ≤ u.points.size
  get : ∀ j : Fin t.points.size, u.points[j.val] = t.points[j.val]

namespace Extends

theorem refl (t : Tree S a) : Extends t t := ⟨Nat.le_refl _, fun _ => rfl⟩

theorem trans {t u v : Tree S a} (htu : Extends t u) (huv : Extends u v) :
    Extends t v :=
  ⟨Nat.le_trans htu.size huv.size, fun j =>
    (huv.get ⟨j.val, Nat.lt_of_lt_of_le j.isLt htu.size⟩).trans (htu.get j)⟩

theorem mem {t u : Tree S a} (h : Extends t u) {x : Fin n} (hx : x ∈ t.points) :
    x ∈ u.points := by
  obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp hx
  rw [← h.get ⟨j, hj⟩]
  exact Array.getElem_mem _

end Extends

theorem push_extends (t : Tree S a) (j : Fin t.points.size) (i : Fin S.size)
    (hnew : S[i.val].get t.points[j.val] ∉ t.points) : Extends t (t.push j i hnew) :=
  ⟨by simp [push], fun k => by simp [push, Array.getElem_push_lt k.isLt]⟩

/-- Inspect one directed edge, appending its target only on first discovery. -/
@[expose] def visit (t : Tree S a) (j : Fin t.points.size) (i : Fin S.size) : Tree S a :=
  if h : t.lookup[(S[i.val].get t.points[j.val]).val] = none then
    t.push j i ((t.missing _).mp h)
  else t

theorem visit_extends (t : Tree S a) (j : Fin t.points.size) (i : Fin S.size) :
    Extends t (t.visit j i) := by
  unfold visit
  split
  · exact t.push_extends j i _
  · exact .refl t

theorem visit_mem (t : Tree S a) (j : Fin t.points.size) (i : Fin S.size) :
    S[i.val].get t.points[j.val] ∈ (t.visit j i).points := by
  unfold visit
  split
  · simp [push]
  · rename_i h
    by_cases hm : S[i.val].get t.points[j.val] ∈ t.points
    · exact hm
    · exact False.elim (h ((t.missing _).mpr hm))

/-- Inspect the generators in their supplied order. Recursive calls carry the
same parent index through the growing queue. -/
@[expose] def scan (t : Tree S a) (j : Fin t.points.size) (gs : List (Fin S.size)) : Tree S a :=
  match gs with
  | [] => t
  | i :: gs =>
    scan (t.visit j i) ⟨j.val, Nat.lt_of_lt_of_le j.isLt (t.visit_extends j i).size⟩ gs

theorem scan_extends (t : Tree S a) (j : Fin t.points.size) (gs : List (Fin S.size)) :
    Extends t (t.scan j gs) := by
  induction gs generalizing t with
  | nil => exact .refl t
  | cons i gs ih => exact (t.visit_extends j i).trans (ih _ _)

theorem scan_mem (t : Tree S a) (j : Fin t.points.size) (gs : List (Fin S.size))
    (i : Fin S.size) (hi : i ∈ gs) : S[i.val].get t.points[j.val] ∈ (t.scan j gs).points := by
  induction gs generalizing t with
  | nil => simp at hi
  | cons g gs ih =>
    have he := t.visit_extends j g
    let k : Fin (t.visit j g).points.size := ⟨j.val, Nat.lt_of_lt_of_le j.isLt he.size⟩
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      exact ((t.visit j g).scan_extends k gs).mem (t.visit_mem j g)
    · simpa only [k, he.get j, scan] using ih (t.visit j g) k hi

/-- The first `cursor` queue entries have had all their edges inspected. -/
@[expose] def Processed (t : Tree S a) (cursor : Nat) : Prop :=
  ∀ j : Fin t.points.size, j.val < cursor →
    ∀ i : Fin S.size, S[i.val].get t.points[j.val] ∈ t.points

theorem scan_processed (t : Tree S a) (cursor : Nat) (hc : cursor < t.points.size)
    (hp : t.Processed cursor) :
    (t.scan ⟨cursor, hc⟩ (List.finRange S.size)).Processed (cursor + 1) := by
  have he := t.scan_extends ⟨cursor, hc⟩ (List.finRange S.size)
  intro j hj i
  have hlt : j.val < t.points.size := by omega
  rw [he.get ⟨j.val, hlt⟩]
  by_cases he : j.val = cursor
  · simpa only [he] using t.scan_mem ⟨cursor, hc⟩ (List.finRange S.size) i (List.mem_finRange i)
  · exact (t.scan_extends ⟨cursor, hc⟩ _).mem
      (hp ⟨j.val, hlt⟩ (by change j.val < cursor; omega) i)

/-- Process each discovered point exactly once. Termination uses the degree,
with the duplicate-free queue proving that no more than `n` points are visited. -/
@[expose] def finish (t : Tree S a) (cursor : Nat) (hp : t.Processed cursor) :
    {u : Tree S a // Extends t u ∧ u.Processed u.points.size} :=
  if hc : cursor < t.points.size then
    let r := t.scan ⟨cursor, hc⟩ (List.finRange S.size)
    let result := finish r (cursor + 1) (t.scan_processed cursor hc hp)
    ⟨result.val, (t.scan_extends ⟨cursor, hc⟩ _).trans result.property.1, result.property.2⟩
  else ⟨t, .refl t, by
    intro j _ i
    exact hp j (by have := j.isLt; omega) i⟩
termination_by n - cursor
decreasing_by have := t.size_le; omega

end Tree

/-- Deterministic breadth-first discovery with constant-time point lookup and
parent edges. Every generator edge from the returned point set stays in it. -/
@[expose] def breadthFirst (S : Array (Perm n)) (a : Fin n) :
    {t : Tree S a // t.Processed t.points.size} :=
  let r := (Tree.root S a).finish 0 (by intro j h; omega)
  ⟨r.val, r.property.2⟩

end Hex.PermGroup.Orbit
