/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CountFrame
public import HexGraphIso.Nauty.Sparse.Scratch
public import HexGraphIso.Nauty.Sparse.Search

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Dividing a cell preserves persistent allocation and generation bounds.
Correctness of the newly written cell indices is established separately. -/
theorem splitCounts_bounded (level first : Nat) (distance : Bool) (s : RefineSt n)
    (h : Scratch.Bounded n s.toScratch) :
    Scratch.Bounded n (splitCounts level first distance s).toScratch := by
  have f := splitCounts_frame level first distance s
  refine ⟨f.starts_size.trans h.starts_size, f.ends_size.trans h.ends_size,
    ?_, ?_, ?_, ?_, ?_⟩
  · change (splitCounts level first distance s).hits.size = n
    rw [f.hits]; exact h.hits_size
  · change (splitCounts level first distance s).marks.size = n
    rw [f.marks]; exact h.marks_size
  · change (splitCounts level first distance s).vmarks.size = n
    rw [f.vmarks]; exact h.vmarks_size
  · intro i hi
    change (splitCounts level first distance s).marks[i]! ≤ _
    rw [f.marks, show (splitCounts level first distance s).toScratch.stamp = s.stamp from f.stamp]
    exact h.marks_le i hi
  · intro i hi
    change (splitCounts level first distance s).vmarks[i]! ≤ _
    rw [f.vmarks, show (splitCounts level first distance s).toScratch.stamp = s.stamp from f.stamp]
    exact h.vmarks_le i hi

/-- The actual search invalidation permits the individualized or recovered
partition while retaining all persistent storage bounds. -/
theorem Storage.invalidate_valid (s : Storage n) (h : Scratch.Bounded n s.scratch)
    (lab ptn : Array Nat) (level : Nat) :
    Scratch.Valid n lab ptn level s.invalidate.scratch :=
  h.invalidate lab ptn level

/-- Canonical installation changes only canonical rows, preserving scratch
validity for the current partition. -/
theorem Storage.update_valid (g : Graph n) (s : Storage n) (lab ptn : Array Nat)
    (level same : Nat) (h : Scratch.Valid n lab ptn level s.scratch) :
    Scratch.Valid n lab ptn level (s.update g lab same).scratch := h

end Hex.GraphIso.Nauty.Sparse
