/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Autos

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

/-- Vertices strictly after the loop cursor. -/
@[expose] def After (cursor : Option Nat) (v : Nat) : Prop :=
  match cursor with
  | none => True
  | some u => u < v

/-- Offset `o` is still eligible after the loop cursor. -/
@[expose] def ChildLive (rsLab : Array Nat) (tc len : Nat) (tcell : VSet n)
    (cursor : Option Nat) (o : Nat) : Prop :=
  o < len ∧ tcell.mem rsLab[tc + o]! = true ∧
    After cursor rsLab[tc + o]!

/-- Cursor eligibility is decidable without asking typeclass search to
reduce the opaque `After` definition. -/
theorem after_or_not (cursor : Option Nat) (v : Nat) :
    After cursor v ∨ ¬ After cursor v := by
  rcases cursor with _ | u
  · exact Or.inl trivial
  · rcases Nat.lt_or_ge u v with h | h
    · exact Or.inl h
    · exact Or.inr (by
        dsimp only [After]
        omega)

/-- A `none` cursor result means that no set member remains after the
cursor. -/
theorem no_child_after {s : VSet n} {cursor : Option Nat}
    (hnext : s.nextElem cursor = none) :
    ∀ v, s.mem v = true → After cursor v → False := by
  intro v hv ha
  have h := VSet.nextElem_none hnext v ?_
  · rw [hv] at h
    cases h
  · rcases cursor with _ | p
    · exact Nat.zero_le _
    · exact ha

/-- A successful `nextElem` lies strictly after its cursor. -/
theorem nextElem_after {s : VSet n} {v : Nat} {cursor : Option Nat}
    (hnext : s.nextElem cursor = some v) : After cursor v := by
  have h := (VSet.nextElem_eq_some_iff.mp hnext).2.1
  rcases cursor with _ | p
  · trivial
  · exact h

/-- `nextElem` returns the least set member strictly after its cursor. -/
theorem nextElem_le {s : VSet n} {v w : Nat} {cursor : Option Nat}
    (hnext : s.nextElem cursor = some v)
    (hw : s.mem w = true) (ha : After cursor w) : v ≤ w := by
  have h := (VSet.nextElem_eq_some_iff.mp hnext).2.2 w
  apply Nat.le_of_not_gt
  intro hlt
  have hz := h ?_ hlt
  · rw [hw] at hz
    cases hz
  · rcases cursor with _ | p
    · exact Nat.zero_le _
    · exact ha

/-- The target-cell representation used by `maketargetcell` is the same
bitset as the length-indexed window representation used by sweep
coverage. -/
theorem worksetOf_eq_windowSet (lab : Array Nat) (tc len : Nat)
    (hlen : 1 ≤ len) :
    worksetOf n lab tc (tc + len - 1) = windowSet n lab tc len := by
  unfold worksetOf windowSet segN
  rw [show tc + len - 1 + 1 - tc = len by omega]
  rw [List.foldl_map]

/-- The start of a sweep always has a first vertex. -/
theorem nextElem_windowSet_some {lab : Array Nat} {tc len : Nat}
    (hlen : 1 ≤ len) (hlt : lab[tc]! < n) :
    ∃ v, (windowSet n lab tc len).nextElem none = some v := by
  rcases hnext : (windowSet n lab tc len).nextElem none with _ | v
  · exfalso
    have hmem : (windowSet n lab tc len).mem lab[tc]! = true := by
      refine mem_windowSet.mpr ⟨hlt, ?_⟩
      rw [segN]
      exact List.mem_map.mpr ⟨0, List.mem_range.mpr (by omega), by simp⟩
    exact no_child_after hnext lab[tc]! hmem trivial
  · exact ⟨v, rfl⟩

end Hex.GraphIso.Nauty
