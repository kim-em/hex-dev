/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.FirstPath
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n k : Nat}

private theorem admit_workperm (st : Search n) :
    (admit st).workperm = st.workperm := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

private theorem pruneReturn_workperm (level : Nat) (st : Search n) :
    (pruneReturn level st).2.workperm = st.workperm := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Leaf actions retain the permutation written by classification. -/
theorem leafExit_workperm (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.workperm = st.workperm := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact admit_workperm _
    | exact pruneReturn_workperm level _

/-- Leaf actions consume the scratch permutation without resizing it. -/
theorem leafExit_workSize (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.workperm.size = st.workperm.size :=
  congrArg Array.size (leafExit_workperm leaf level st)

/-- Classifying a node may replace scratch entries but preserves its allocation. -/
theorem classify_workSize (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.workperm.size = st.workperm.size := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite (fun s : Search n => s.workperm.size), scatter_size, ite_self]

/-- The off-path operations preserve the scratch allocation exactly. -/
theorem scratchPolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.ReferencePolicy ctx inf tcLevel (fun st : Search n => st.workperm.size) where
  visit := fun _ _ _ => rfl
  compare := by
    intro level code st
    change (compareCodes level code st).workperm.size = st.workperm.size
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run,
      apply_ite (fun s : Search n => s.workperm.size), ite_self]
  target := by
    intro level numcells st
    change (chooseTarget false ctx tcLevel level numcells st).2.2.2.workperm.size = st.workperm.size
    rw [chooseTarget_fields]
  classify := classify_workSize ctx
  leaf := leafExit_workSize
  cheap := by
    intro first level st
    change (cheapCheck first level st).workperm.size = st.workperm.size
    unfold cheapCheck
    split <;> rfl
  child := by intro first level tc tv st; cases first <;> rfl
  leave := fun _ _ => rfl
  recover := by
    intro level st
    change (recoverLevels level (recoverPtn inf level st)).workperm.size = st.workperm.size
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite (fun s : Search n => s.workperm.size), ite_self]
  afterSweep := by
    intro first level size index st
    change (afterSweep first level size index st).workperm.size = st.workperm.size
    unfold afterSweep
    split <;> rfl

/-- An off-path node uses the allocated scratch array throughout the call. -/
theorem node_workSize (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n) :
    (node false ctx inf tcLevel fuel level numcells st).2.workperm.size = st.workperm.size := by
  rw [node_eq_generic]
  exact Generic.node_reference (scratchPolicy ctx inf tcLevel) fuel level numcells st

/-- Later siblings retain the same scratch allocation. -/
theorem sweep_workSize (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : Search n)
    (hpast : Generic.Past first tv1 cursor) :
    (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.workperm.size =
      st.workperm.size := by
  rw [sweep_eq_generic]
  exact Generic.sweep_reference (scratchPolicy ctx inf tcLevel) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast

/-- The first descent does not use or resize the scratch allocation. -/
theorem firstPath_workSize {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n} (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    (node true ctx inf tcLevel fuel level numcells st).2.workperm.size = st.workperm.size := by
  rw [node_eq_generic]
  have heq := hpath.reference (scratchPolicy ctx inf tcLevel) (fun _ _ _ => rfl)
  rw [heq]
  clear heq
  change leaf.workperm.size = st.workperm.size
  have hprepare : ∀ level numcells (st : Search n),
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.workperm.size = st.workperm.size := by
    intro level numcells st
    unfold Generic.prepareFirst
    change (chooseTarget true ctx tcLevel level _ _).2.2.2.workperm.size = _
    rw [chooseFirst_fields]
    rfl
  induction hpath with
  | leaf fuel level numcells st hdisc => exact hprepare level numcells st
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).workperm.size = _
    unfold cheapCheck
    split <;> exact hprepare level numcells st

/-- Every scratch scatter in a complete engine run has its initial allocation size. -/
theorem runState_workSize (G : Colored n k) :
    (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2.workperm.size = n := by
  by_cases hn0 : n = 0
  · subst n
    simp only [runState, initial, beq_self_eq_true, ite_true, Array.size_replicate]
  · obtain ⟨last, leaf, hpath⟩ := initial_path G (by omega)
    rw [runState, ite_eq_right (by simpa using hn0), firstPath_workSize hpath]
    exact Array.size_replicate

end Hex.GraphIso.Nauty
