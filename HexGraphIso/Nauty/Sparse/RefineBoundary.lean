/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Boundary
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

theorem splitSingleton_boundary (g : Graph n) (level split : Nat) (s : RefineSt n) :
    Boundary level s.ptn (splitSingleton g level split s).ptn := by
  unfold splitSingleton
  simp only
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Boundary level s.ptn t.ptn)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜Boundary level s.ptn state.ptn⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.push] <;>
      grind [Boundary.refl, Boundary.set]

theorem splitNontrivial_boundary (g : Graph n) (level split : Nat) (s : RefineSt n) :
    Boundary level s.ptn (splitNontrivial g level split s).ptn := by
  unfold splitNontrivial
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Boundary level s.ptn t.ptn)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜Boundary level s.ptn state.ptn⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash] <;>
      grind [Boundary.refl, Boundary.trans, splitCounts_boundary]

/-- Distance refinement and the full active-cell loop preserve the allocation
and existing closed boundaries of the incoming partition. -/
theorem refineWith_boundary (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch) :
    Boundary level ptn (refineWith g level lab ptn active numcells scratch).ptn := by
  unfold refineWith
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Boundary level ptn t.ptn)
  mvcgen
  all_goals first
    | exact (⇓⟨_, state⟩ => ⌜Boundary level ptn state.1.ptn⌝)
    | exact (⇓⟨_, state⟩ => ⌜Boundary level ptn state.ptn⌝)
    | exact (⇓⟨_, _⟩ => ⌜True⌝)
    | skip
  all_goals
    simp_all +zetaDelta [RefineSt.hash] <;>
      try grind [Boundary.refl, Boundary.trans, splitCounts_boundary,
        splitSingleton_boundary, splitNontrivial_boundary]
  all_goals first
    | (refine Boundary.trans ?_ (splitSingleton_boundary _ _ _ _); assumption)
    | (refine Boundary.trans ?_ (splitNontrivial_boundary _ _ _ _); assumption)

end Hex.GraphIso.Nauty.Sparse
