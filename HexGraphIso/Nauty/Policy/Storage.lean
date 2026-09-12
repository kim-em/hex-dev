/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.SearchState

variable {n : Nat} {κ : Type}

/-- Code bookkeeping preserves arbitrary canonical storage. -/
theorem compare_storage (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).canong = st.canong := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.canong, ite_self]

theorem terminal_storage (level : Nat) (st : SearchState n κ) :
    (firstterminal level st).canong = st.canong := by
  unfold firstterminal
  rfl

theorem scatter_storage (ref : Array Nat) (st : SearchState n κ) :
    (scatter ref st).canong = st.canong := by
  unfold scatter
  rfl

theorem push_storage (st : SearchState n κ) (pair : VSet n × VSet n) :
    (pushAuto st pair).canong = st.canong := by
  unfold pushAuto
  split <;> rfl

theorem admit_storage (st : SearchState n κ) : (admit st).canong = st.canong := by
  simp only [admit, Id.run_pure, push_storage]

theorem prune_storage (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.canong = st.canong := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite SearchState.canong, push_storage, ite_self]

/-- Every classification exit preserves storage while updating the selected
label, row-prefix counter, automorphism trace and return controls. -/
theorem leaf_storage (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.canong = st.canong := by
  unfold leafExit
  cases leaf <;>
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
      apply_ite SearchState.canong, prune_storage, admit_storage, install, ite_self]

end Hex.GraphIso.Nauty.SearchState
