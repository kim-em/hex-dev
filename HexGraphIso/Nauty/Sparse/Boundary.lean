/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Refine
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Refinement only writes its current level into the partition array. -/
structure Boundary (level : Nat) (before after : Array Nat) : Prop where
  size : after.size = before.size
  values : ∀ q : Nat, after[q]! = before[q]! ∨ after[q]! = level

namespace Boundary

theorem refl (level : Nat) (ptn : Array Nat) : Boundary level ptn ptn :=
  ⟨rfl, fun _ => Or.inl rfl⟩

theorem trans (h : Boundary level a b) (h' : Boundary level b c) :
    Boundary level a c := by
  refine ⟨h'.size.trans h.size, fun q => ?_⟩
  rcases h'.values q with he | he
  · rw [he]
    exact h.values q
  · exact Or.inr he

theorem set (h : Boundary level a b) (i : Nat) :
    Boundary level a (b.setIfInBounds i level) := by
  change Boundary level a (b.set! i level)
  refine ⟨by simpa using h.size, fun q => ?_⟩
  by_cases he : q = i
  · subst q
    by_cases hi : i < b.size
    · simp [hi]
    · simpa [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le,
        Nat.le_of_not_lt hi] using h.values i
  · simpa only [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he)] using h.values q

theorem closed (h : Boundary level a b) {q : Nat} (hq : a[q]! ≤ level) : b[q]! ≤ level := by
  rcases h.values q with he | he <;> omega

end Boundary

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 2000000

/-- The complete count splitter preserves old closed boundaries, including
all indirect-sort, queue-replacement and distance-code branches. -/
theorem splitCounts_boundary (level first : Nat) (distance : Bool) (s : RefineSt n) :
    Boundary level s.ptn (splitCounts level first distance s).ptn := by
  unfold splitCounts CountSort.firstRun CountSort.minima CountSort.finish
  simp only [Id.run]
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Boundary level s.ptn t.ptn)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜Boundary level s.ptn state.1.ptn⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [Boundary.refl, Boundary.set]

end Hex.GraphIso.Nauty.Sparse
