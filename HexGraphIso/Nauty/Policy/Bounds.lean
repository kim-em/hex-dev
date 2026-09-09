/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Bounded
public import HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- First-code comparison advances only from agreement at the preceding level. -/
theorem compareCodes_eqlev (level code : Nat) (st : Search n) :
    (compareCodes level code st).eqlevFirst =
      if st.eqlevFirst = level - 1 ∧ code = st.firstcode[level]! then level else st.eqlevFirst := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.eqlevFirst, ite_self,
    beq_iff_eq]

/-- Once first-code agreement has diverged above a frame, descendants cannot restore it. -/
theorem divergencePolicy (ctx : Ctx n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy ctx inf tcLevel bound (fun st : Search n => st.eqlevFirst < bound) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st hlevel h
    change (compareCodes level code st).eqlevFirst < bound
    rw [compareCodes_eqlev, ite_eq_right (by omega)]
    exact h
  target := by
    intro level numcells st _ h
    exact Nat.lt_of_le_of_lt (chooseTarget_le ctx tcLevel level numcells st) h
  classify := by
    intro level numcells st h
    change (classify ctx level numcells st).2.eqlevFirst < bound
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
    change (afterSweep first level size index st).eqlevFirst < bound
    unfold afterSweep
    split <;> exact h

/-- An off-path call retains divergence above its entry frame. -/
theorem node_diverged {ctx : Ctx n} {inf tcLevel fuel level numcells bound : Nat}
    {st : Search n} (hlevel : bound < level) (h : st.eqlevFirst < bound) :
    (node false ctx inf tcLevel fuel level numcells st).2.eqlevFirst < bound := by
  rw [node_eq_generic]
  exact Generic.node_bounded (divergencePolicy ctx inf tcLevel bound) fuel level numcells st hlevel h

/-- Later siblings retain divergence above their parent frame. -/
theorem sweep_diverged {ctx : Ctx n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index bound : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (hpast : Generic.Past first tv1 cursor) (hlevel : bound ≤ level)
    (h : st.eqlevFirst < bound) :
    (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.eqlevFirst < bound := by
  rw [sweep_eq_generic]
  exact Generic.sweep_bounded (divergencePolicy ctx inf tcLevel bound) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast hlevel h

private theorem admit_noncheap (st : Search n) :
    (admit st).noncheaplevel = st.noncheaplevel := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

private theorem pruneReturn_noncheap (level : Nat) (st : Search n) :
    (pruneReturn level st).2.noncheaplevel = st.noncheaplevel := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Classifying or acting on a leaf does not move the cheap boundary. -/
theorem leafExit_noncheap (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.noncheaplevel = st.noncheaplevel := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact admit_noncheap _
    | exact pruneReturn_noncheap level _

/-- Recovery leaves a failed guard strictly below the recovered parent. -/
theorem recover_noncheap (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).noncheaplevel =
      if level < st.noncheaplevel then level + 1 else st.noncheaplevel := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]

/-- Searching below a noncheap ancestor cannot turn that ancestor cheap. -/
theorem noncheapPolicy (ctx : Ctx n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy ctx inf tcLevel bound (fun st : Search n => bound < st.noncheaplevel) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change bound < (compareCodes level code st).noncheaplevel
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.noncheaplevel, ite_self]
    exact h
  target := by
    intro level numcells st _ h
    change bound < (chooseTarget false ctx tcLevel level numcells st).2.2.2.noncheaplevel
    rw [chooseTarget_fields]
    exact h
  classify := by
    intro level numcells st h
    change bound < (classify ctx level numcells st).2.noncheaplevel
    unfold classify
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
      apply_ite Search.noncheaplevel, ite_self]
    exact h
  leaf := by
    intro leaf level st _ h
    change bound < (leafExit leaf level st).2.noncheaplevel
    rw [leafExit_noncheap]
    exact h
  cheap := by
    intro first level st hlevel h
    change bound < (cheapCheck first level st).noncheaplevel
    unfold cheapCheck
    split
    · change bound < level + 1
      omega
    · exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hlevel h
    change bound < (recoverLevels level (recoverPtn inf level st)).noncheaplevel
    rw [recover_noncheap]
    split <;> omega
  afterSweep := by
    intro first level size index st _ h
    change bound < (afterSweep first level size index st).noncheaplevel
    unfold afterSweep
    split <;> exact h

/-- A noncheap ancestor stays noncheap throughout an off-path descendant call. -/
theorem node_noncheap {ctx : Ctx n} {inf tcLevel fuel level numcells bound : Nat}
    {st : Search n} (hlevel : bound < level) (h : bound < st.noncheaplevel) :
    bound < (node false ctx inf tcLevel fuel level numcells st).2.noncheaplevel := by
  rw [node_eq_generic]
  exact Generic.node_bounded (noncheapPolicy ctx inf tcLevel bound) fuel level numcells st hlevel h

/-- A later-sibling sweep preserves the failed guard at an ancestor. -/
theorem sweep_noncheap {ctx : Ctx n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index bound : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (hpast : Generic.Past first tv1 cursor) (hlevel : bound ≤ level)
    (h : bound < st.noncheaplevel) :
    bound < (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.noncheaplevel := by
  rw [sweep_eq_generic]
  exact Generic.sweep_bounded (noncheapPolicy ctx inf tcLevel bound) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast hlevel h

end Hex.GraphIso.Nauty
