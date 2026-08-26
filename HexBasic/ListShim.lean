/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Mathlib-free list helpers used by the Hex libraries.

The compatibility declarations this module previously reproduced from Batteries
(`pairwise_lt_finRange`, `nodup_finRange`, `perm_ext_iff_of_nodup`, and the
`idxOf` lemmas) entered Lean core in v4.33 and no longer belong here.
-/

namespace List

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
