/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Controls
import all HexGraphIso.Nauty.Policy.Generic.Bounded
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A saved cheap boundary above the receiving ancestor is either retained
literally or replaced strictly below that ancestor by the actual sparse policy. -/
theorem boundaryPolicy (g : Graph n) (inf tcLevel bound saved : Nat) :
    Generic.BoundedPolicy g inf tcLevel bound
      (fun st : State n => st.noncheaplevel = saved ∨ bound < st.noncheaplevel) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change (compareCodes level code st).noncheaplevel = saved ∨ bound < (compareCodes level code st).noncheaplevel
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
    exact h
  target := by
    intro level numcells st _ h
    change (chooseTarget false g tcLevel level numcells st).2.2.2.noncheaplevel = saved ∨
      bound < (chooseTarget false g tcLevel level numcells st).2.2.2.noncheaplevel
    rw [(chooseTarget_controls false g tcLevel level numcells st).2]
    exact h
  classify := by
    intro level numcells st h
    change (classify g level numcells st).2.noncheaplevel = saved ∨
      bound < (classify g level numcells st).2.noncheaplevel
    rw [(classify_controls g level numcells st).2]
    exact h
  leaf := by
    intro leaf level st _ h
    change (leafExit leaf level st).2.noncheaplevel = saved ∨ bound < (leafExit leaf level st).2.noncheaplevel
    rw [leafExit_noncheap]
    exact h
  cheap := by
    intro first level st hl h
    change (cheapCheck first level st).noncheaplevel = saved ∨ bound < (cheapCheck first level st).noncheaplevel
    unfold cheapCheck
    split
    · exact Or.inr (by change bound < level + 1; omega)
    · exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hl h
    change (Nauty.recover inf level st).noncheaplevel = saved ∨
      bound < (Nauty.recover inf level st).noncheaplevel
    rw [recover_noncheap]
    split
    · exact Or.inr (by omega)
    · exact h
  afterSweep := by
    intro first level size index st _ h
    change (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).noncheaplevel = saved ∨
      bound < (if first then { (Nauty.afterSweep first level size index st) with
        order := (Nauty.afterSweep first level size index st).order * index }
        else Nauty.afterSweep first level size index st).noncheaplevel
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h

/-- An off-path native call can change an older cheap boundary only at or
below its own depth, including truncated calls and nonlocal returns. -/
theorem node_boundary (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n)
    (hl : 0 < level) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.noncheaplevel = st.noncheaplevel ∨
      level ≤ (Generic.node false g inf tcLevel fuel level numcells st).2.noncheaplevel := by
  have h := Generic.node_bounded (boundaryPolicy g inf tcLevel (level - 1) st.noncheaplevel)
    fuel level numcells st (by omega) (Or.inl rfl)
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (by omega)

end Hex.GraphIso.Nauty.Sparse
