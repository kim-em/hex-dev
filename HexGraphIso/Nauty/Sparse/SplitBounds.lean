/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Marks
public import HexGraphIso.Nauty.Sparse.ScratchSearch
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- The complete singleton pass preserves persistent allocation and generation
bounds, including the borrowed arrays and reverse scatter of hit vertices. -/
theorem splitSingleton_bounded (g : Graph n) (level split : Nat) (s : RefineSt n)
    (h : Scratch.Bounded n s.toScratch) :
    Scratch.Bounded n (splitSingleton g level split s).toScratch := by
  unfold splitSingleton
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Scratch.Bounded n t.toScratch)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Bounded n state.toScratch⌝)
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Marks n (s.stamp + 1)
          (state : Array Nat × Array Nat × Array Nat).1 ∧
          Scratch.Marks n (s.stamp + 1) state.2.2⌝)
      | exact (⇓⟨_, state⟩ => ⌜(state.2.1 : Array Nat).size = n⌝)
      | exact (⇓⟨_, _⟩ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push, RefineSt.toScratch]
    try grind [Scratch.Bounded, Scratch.Marks, Scratch.Marks.set]

/-- First-touch clearing, neighbour accumulation, and all following count
splits preserve the persistent scratch allocation and generation bounds. -/
theorem splitNontrivial_bounded (g : Graph n) (level split : Nat) (s : RefineSt n)
    (h : Scratch.Bounded n s.toScratch) :
    Scratch.Bounded n (splitNontrivial g level split s).toScratch := by
  unfold splitNontrivial
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Scratch.Bounded n t.toScratch)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Bounded n state.toScratch⌝)
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Marks n (s.stamp + 1) state.1 ∧
          (state.2.1 : Array Nat).size = n⌝)
      | exact (⇓⟨_, state⟩ => ⌜(state : Array Nat).size = n⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.toScratch]
    try grind [Scratch.Bounded, Scratch.Marks, Scratch.Marks.set]
  all_goals
    apply splitCounts_bounded
    assumption

end Hex.GraphIso.Nauty.Sparse
