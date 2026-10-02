/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Depth
public import HexGraphIso.Nauty.Policy.Generic.Bounded
import all HexGraphIso.Nauty.Policy.Generic.Bounded
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The shared comparison advances only from agreement at the preceding
level, applied to the actual native search state. -/
theorem compareCodes_eqlev (level code : Nat) (st : State n) :
    (compareCodes level code st).eqlevFirst =
      if st.eqlevFirst = level - 1 ∧ code = st.firstcode[level]! then level else st.eqlevFirst := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.eqlevFirst, ite_self, beq_iff_eq]

/-- Native descendants cannot restore first-code agreement lost strictly
above their receiving ancestor. -/
theorem divergencePolicy (g : Graph n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy g inf tcLevel bound (fun st : State n => st.eqlevFirst < bound) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st hlevel h
    change (compareCodes level code st).eqlevFirst < bound
    rw [compareCodes_eqlev, ite_eq_right (by omega)]
    exact h
  target := by
    intro level numcells st _ h
    exact Nat.lt_of_le_of_lt (chooseTarget_le g tcLevel level numcells st) h
  classify := by
    intro level numcells st h
    change (classify g level numcells st).2.eqlevFirst < bound
    rw [classify_eqlev]
    exact h
  leaf := by
    intro leaf level st _ h
    change (leafExit leaf level st).2.eqlevFirst < bound
    rw [leafExit_eqlev]
    exact h
  cheap := by
    intro first level st _ h
    change (cheapCheck first level st).eqlevFirst < bound
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st _ h
    exact Nat.lt_of_le_of_lt (recover_le inf level st) h
  afterSweep := by
    intro first level size index st _ h
    change (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).eqlevFirst < bound
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h

theorem node_diverged {g : Graph n} {inf tcLevel fuel level numcells bound : Nat} {st : State n}
    (hlevel : bound < level) (h : st.eqlevFirst < bound) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.eqlevFirst < bound :=
  Generic.node_bounded (divergencePolicy g inf tcLevel bound) fuel level numcells st hlevel h

theorem sweep_diverged {g : Graph n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index bound : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : State n} (hpast : Generic.Past first tv1 cursor) (hlevel : bound ≤ level)
    (h : st.eqlevFirst < bound) :
    (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.eqlevFirst < bound :=
  Generic.sweep_bounded (divergencePolicy g inf tcLevel bound) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast hlevel h

end Hex.GraphIso.Nauty.Sparse
