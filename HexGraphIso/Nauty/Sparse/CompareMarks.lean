/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CompareRow

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The current generation marks exactly the specified vertices. -/
structure Marks (n stamp : Nat) (a : Array Nat) (member : Nat → Prop) : Prop where
  size : a.size = n
  bound : ∀ v, v < n → a[v]! ≤ stamp
  marked : ∀ v, v < n → (a[v]! = stamp ↔ member v)

namespace Marks

variable {n stamp : Nat} {a : Array Nat} {member : Nat → Prop}

theorem fresh (hs : a.size = n) (hb : ∀ v, v < n → a[v]! < stamp) :
    Marks n stamp a (fun _ => False) := by
  refine ⟨hs, fun v hv => Nat.le_of_lt (hb v hv), ?_⟩
  intro v hv
  have := hb v hv
  simp only [iff_false]
  omega

theorem congr (h : Marks n stamp a member) {other : Nat → Prop}
    (he : ∀ v, v < n → (member v ↔ other v)) : Marks n stamp a other :=
  ⟨h.size, h.bound, fun v hv => (h.marked v hv).trans (he v hv)⟩

theorem set (h : Marks n stamp a member) {v : Nat} (hv : v < n) :
    Marks n stamp (a.set! v stamp) (fun w => member w ∨ w = v) := by
  refine ⟨by simp [h.size], ?_, ?_⟩
  · intro w hw
    by_cases he : v = w
    · subst w
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hv)]
      exact Nat.le_refl _
    · rw [Array.getElem!_set!_ne _ _ _ _ he]
      exact h.bound w hw
  · intro w hw
    by_cases he : v = w
    · subst w
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hv)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ he, h.marked w hw]
      simp [Ne.symm he]

theorem clear (h : Marks n stamp a member) (hs : 0 < stamp) {v : Nat} (hv : v < n) :
    Marks n stamp (a.set! v 0) (fun w => member w ∧ w ≠ v) := by
  refine ⟨by simp [h.size], ?_, ?_⟩
  · intro w hw
    by_cases he : v = w
    · subst w
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hv)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ he]
      exact h.bound w hw
  · intro w hw
    by_cases he : v = w
    · subst w
      rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hv)]
      simp
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ he, h.marked w hw]
      simp [Ne.symm he]

end Marks

/-- During candidate scanning, the live marks describe old-only vertices;
`mina` is the least candidate-only vertex encountered, or the sentinel. -/
structure Diff (n stamp : Nat) (old seen : List Nat) (a : Array Nat) (mina : Nat) : Prop where
  marks : Marks n stamp a (fun v => v ∈ old ∧ v ∉ seen)
  seen_lt : ∀ v ∈ seen, v < n
  min_le : mina ≤ n
  witness : mina < n → mina ∈ seen ∧ mina ∉ old
  least : ∀ v ∈ seen, v ∉ old → mina ≤ v

namespace Diff

variable {n stamp : Nat} {old seen : List Nat} {a : Array Nat} {mina v : Nat}

theorem initial (h : Marks n stamp a (· ∈ old)) : Diff n stamp old [] a n := by
  refine ⟨h.congr (by simp), by simp, by omega, ?_, by simp⟩
  omega

theorem hit (h : Diff n stamp old seen a mina) (hs : 0 < stamp)
    (hv : v < n) (hmark : a[v]! = stamp) :
    Diff n stamp old (seen ++ [v]) (a.set! v 0) mina := by
  have hm := (h.marks.marked v hv).mp hmark
  refine ⟨(h.marks.clear hs hv).congr (by simp [and_assoc]), ?_, h.min_le, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.seen_lt w hw
    · exact hv
  · intro hl
    have hw := h.witness hl
    exact ⟨List.mem_append_left _ hw.1, hw.2⟩
  · intro w hw hn
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.least w hw hn
    · exact False.elim (hn hm.1)

theorem miss (h : Diff n stamp old seen a mina) (hv : v < n) (hn : v ∉ seen)
    (hmark : a[v]! ≠ stamp) :
    Diff n stamp old (seen ++ [v]) a (min mina v) := by
  have ho : v ∉ old := fun ho => hmark ((h.marks.marked v hv).mpr ⟨ho, hn⟩)
  refine ⟨h.marks.congr ?_, ?_, by have := h.min_le; omega, ?_, ?_⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton, not_or]
    constructor
    · intro hm
      refine ⟨hm.1, hm.2, ?_⟩
      intro he
      exact ho (he ▸ hm.1)
    · exact fun hm => ⟨hm.1, hm.2.1⟩
  · intro w hw
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · exact h.seen_lt w hw
    · exact hv
  · intro hl
    by_cases hm : mina ≤ v
    · rw [Nat.min_eq_left hm]
      have hw := h.witness (by omega)
      exact ⟨List.mem_append_left _ hw.1, hw.2⟩
    · rw [Nat.min_eq_right (by omega)]
      exact ⟨by simp, ho⟩
  · intro w hw hnot
    simp only [List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have := h.least w hw hnot
      omega
    · omega

theorem sentinel (h : Diff n stamp old seen a mina) (hm : mina = n) : seen ⊆ old := by
  intro v hv
  by_cases hn : v ∈ old
  · exact hn
  · have := h.seen_lt v hv
    have := h.least v hv hn
    omega

end Diff

end Hex.GraphIso.Nauty.Sparse
