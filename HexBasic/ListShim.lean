/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Lemmas reproduced from Batteries.

These are the `Batteries` lemmas the Mathlib-free `hex` libraries (`HexMatrix`,
`HexRowReduce`, `HexDeterminant`, `HexGramSchmidt`, `HexBerlekamp`) relied on but
which are not (yet) in the Lean core library. They are reproduced here, with
names and signatures identical to the Batteries originals, so the Mathlib-free
libraries do not need to depend on Batteries.

Keeping the signatures identical to Batteries is deliberate: the `*Mathlib`
bridge libraries pull Batteries in via Mathlib, so both copies coexist there.
Lean accepts duplicate declarations from different modules when their signatures
match (the proofs may differ), so there is no clash. If you change a signature
here it will collide with Batteries in the bridge libraries.
-/

namespace List

/-- The `Batteries.Data.List.Lemmas` strict-order property for `List.finRange`. -/
theorem pairwise_lt_finRange (n : Nat) : Pairwise (· < ·) (finRange n) := by
  rw [pairwise_iff_getElem]
  intro i j hi hj hlt
  simp only [getElem_finRange]
  exact hlt

/-- `List.finRange` contains no duplicate indices. -/
theorem nodup_finRange (n : Nat) : (finRange n).Nodup :=
  (pairwise_lt_finRange n).imp Fin.ne_of_lt

/-- Two duplicate-free lists are permutations exactly when they have the same elements.
The Batteries original has no `[DecidableEq α]`; we match that signature and use
`classical` in the proof, since core lacks the `Subperm` API Batteries uses. -/
theorem perm_ext_iff_of_nodup {α} {l₁ l₂ : List α}
    (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) : l₁ ~ l₂ ↔ ∀ a, a ∈ l₁ ↔ a ∈ l₂ := by
  classical
  rw [perm_iff_count]
  refine ⟨fun h a => by rw [← count_pos_iff, ← count_pos_iff, h], fun h a => ?_⟩
  rw [d₁.count, d₂.count]
  simp only [h a]

/-- Indexing a list at the position returned by {name}`idxOf` recovers the element. -/
@[simp, grind =]
theorem getElem_idxOf [BEq α] [LawfulBEq α] {x : α} {xs : List α}
    (h : idxOf x xs < xs.length) : xs[xs.idxOf x] = x := by
  induction xs <;> grind

/-- In a duplicate-free list, {name}`idxOf` recovers the index of an element. -/
@[simp, grind =]
theorem Nodup.idxOf_getElem [BEq α] [LawfulBEq α] {xs : List α} (H : Nodup xs)
    (i : Nat) (h : i < xs.length) : idxOf xs[i] xs = i := by
  induction xs generalizing i <;> grind

/-- A `Nodup` list contained in another list is no longer than it. Replaces uses
of `Batteries`' `Subperm` API (`subperm_of_subset`/`Subperm.length_le`), which
core lacks; unlike the declarations above, this name is local to Hex. -/
theorem nodup_subset_length_le {α} [DecidableEq α] {l₁ l₂ : List α}
    (h₁ : l₁.Nodup) (hsub : l₁ ⊆ l₂) : l₁.length ≤ l₂.length := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    rw [nodup_cons] at h₁
    have ha : a ∈ l₂ := hsub (mem_cons_self ..)
    have htsub : t ⊆ l₂.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => h₁.1 (h ▸ hx)
      exact (mem_erase_of_ne hxa).2 (hsub (mem_cons_of_mem _ hx))
    have hih := ih h₁.2 htsub
    have hlen : (l₂.erase a).length = l₂.length - 1 := by rw [length_erase]; simp [ha]
    have hpos : 1 ≤ l₂.length := length_pos_of_mem ha
    simp only [length_cons]; omega

end List
