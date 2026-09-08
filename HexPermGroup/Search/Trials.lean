/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Perm

public section

namespace Hex.PermGroup.Search

/-- A finite sequence of refinement reasons, constructed by index. Even a
quadratic family can be searched under a small budget without allocating it. -/
structure Trials (α : Type) where
  size : Nat
  get : Fin size → α

namespace Trials

@[expose] def empty : Trials α := ⟨0, Fin.elim0⟩
@[expose] def singleton (x : α) : Trials α := ⟨1, fun _ => x⟩
@[expose] def range (n : Nat) : Trials (Fin n) := ⟨n, id⟩
@[expose] def map (f : α → β) (t : Trials α) : Trials β := ⟨t.size, fun i => f (t.get i)⟩

@[expose] def append (s t : Trials α) : Trials α where
  size := s.size + t.size
  get i := if h : i.val < s.size then s.get ⟨i.val, h⟩ else t.get ⟨i.val - s.size, by omega⟩

/-- Row-major candidate order, without constructing a list of pairs. -/
@[expose] def product (s : Trials α) (t : Trials β) : Trials (α × β) where
  size := s.size * t.size
  get i :=
    have ht : 0 < t.size := by
      by_cases h : t.size = 0
      · simp [h] at i
        exact Fin.elim0 i
      · omega
    (s.get ⟨i.val / t.size, (Nat.div_lt_iff_lt_mul ht).mpr i.isLt⟩,
      t.get ⟨i.val % t.size, Nat.mod_lt _ ht⟩)

/-- A scan either finds the first successful test, checks every remaining
test, or stops with no completeness claim. -/
inductive Result (t : Trials α) (test : α → Bool) (start : Nat) where
  | found (i : Fin t.size) (after : start ≤ i.val) (valid : test (t.get i) = true)
      (earlier : ∀ j : Fin t.size, start ≤ j.val → j.val < i.val → test (t.get j) = false)
  | clear (checked : ∀ i : Fin t.size, start ≤ i.val → test (t.get i) = false)
  | incomplete

/-- `used` counts calls of the refinement test. An incomplete scan has spent
its entire allowance and still has an unvisited candidate. -/
structure Run (t : Trials α) (test : α → Bool) (start capacity : Nat) where
  result : Result t test start
  used : Nat
  bounded : used ≤ capacity
  depleted : result = .incomplete → used = capacity
  unfinished : result = .incomplete → start + used < t.size

variable {t : Trials α} {test : α → Bool} {start capacity : Nat}

@[expose] def advance (hs : start < t.size) (h : test (t.get ⟨start, hs⟩) = false)
    (r : Run t test (start + 1) capacity) : Run t test start (capacity + 1) :=
  match r with
  | ⟨.found i hi ht he, used, bound, _, _⟩ =>
    { result := .found i (by omega) ht (by
        intro j hj hji
        by_cases heq : j.val = start
        · have hj' : j = ⟨start, hs⟩ := Fin.ext heq
          simpa only [hj'] using h
        · exact he j (by omega) hji)
      used := used + 1
      bounded := Nat.succ_le_succ bound
      depleted := by intro h; cases h
      unfinished := by intro h; cases h }
  | ⟨.clear checked, used, bound, _, _⟩ =>
    { result := .clear (by
        intro j hj
        by_cases heq : j.val = start
        · have hj' : j = ⟨start, hs⟩ := Fin.ext heq
          simpa only [hj'] using h
        · exact checked j (by omega))
      used := used + 1
      bounded := Nat.succ_le_succ bound
      depleted := by intro h; cases h
      unfinished := by intro h; cases h }
  | ⟨.incomplete, used, bound, depleted, unfinished⟩ =>
    { result := .incomplete
      used := used + 1
      bounded := Nat.succ_le_succ bound
      depleted := fun _ => congrArg (· + 1) (depleted rfl)
      unfinished := fun _ => by have hi := unfinished rfl; omega }

/-- Stop before the next test if the allowance is exhausted. Reaching the end
of an empty candidate suffix needs no allowance and proves completeness. -/
@[expose] def scan (t : Trials α) (test : α → Bool) (start capacity : Nat) : Run t test start capacity :=
  if hs : start < t.size then
    match capacity with
    | 0 =>
      { result := .incomplete
        used := 0
        bounded := Nat.le_refl _
        depleted := fun _ => rfl
        unfinished := fun _ => hs }
    | capacity + 1 =>
      if h : test (t.get ⟨start, hs⟩) = true then
        { result := .found ⟨start, hs⟩ (Nat.le_refl _) h (by
            intro j hj hji
            change j.val < start at hji
            omega)
          used := 1
          bounded := by omega
          depleted := by intro h; cases h
          unfinished := by intro h; cases h }
      else advance hs (Bool.eq_false_iff.mpr h) (scan t test (start + 1) capacity)
  else
    { result := .clear (by intro i hi; omega)
      used := 0
      bounded := Nat.zero_le _
      depleted := by intro h; cases h
      unfinished := by intro h; cases h }

theorem scan_complete (t : Trials α) (test : α → Bool) :
    (t.scan test 0 t.size).result ≠ .incomplete := by
  intro h
  have hd := (t.scan test 0 t.size).depleted h
  have hu := (t.scan test 0 t.size).unfinished h
  omega

/-- Unbounded refinement discovery uses precisely the same scan as its
budgeted counterpart, with enough allowance for every candidate. -/
@[expose] def find (t : Trials α) (test : α → Bool) : Option α :=
  match (t.scan test 0 t.size).result with
  | .found i _ _ _ => some (t.get i)
  | .clear _ => none
  | .incomplete => none

theorem find_checked (t : Trials α) (test : α → Bool) (x : α) (h : t.find test = some x) : test x = true := by
  unfold find at h
  split at h
  · rename_i i _ hi _ _
    cases h
    exact hi
  · cases h
  · cases h

theorem find_none (t : Trials α) (test : α → Bool) :
    t.find test = none ↔ ∀ i : Fin t.size, test (t.get i) = false := by
  unfold find
  cases hr : (t.scan test 0 t.size).result with
  | found i _ hi _ =>
    constructor
    · intro h; cases h
    · intro h
      have he := h i
      rw [hi] at he
      cases he
  | clear checked => exact ⟨fun _ i => checked i (Nat.zero_le _), fun _ => rfl⟩
  | incomplete => exact False.elim (t.scan_complete test hr)

end Trials

end Hex.PermGroup.Search
