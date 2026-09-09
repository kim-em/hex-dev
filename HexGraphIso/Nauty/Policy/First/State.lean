/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Generic.Reference
public import HexGraphIso.Nauty.Policy.Instance
public import HexGraphIso.Nauty.Policy.Target
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State
import all HexGraphIso.Nauty.Policy.Instance

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- The saved first-path codes, target positions, and leaf labelling. -/
def Search.reference (st : Search n) : Array Nat × Array Int × Array Nat :=
  (st.firstcode, st.firsttc, st.firstlab)

/-- Workspace insertion preserves the first-path reference. -/
theorem pushAuto_reference (st : Search n) (pair : VSet n × VSet n) :
    (pushAuto st pair).reference = st.reference := by
  unfold pushAuto
  split <;> rfl

/-- Scratch construction preserves the first-path reference. -/
theorem scatter_reference (ref : Array Nat) (st : Search n) :
    (scatter ref st).reference = st.reference := by
  rw [scatter_eq]
  rfl

/-- Classifying a node never replaces the first-path reference. -/
theorem classify_reference (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.reference = st.reference := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    Search.reference, apply_ite Search.firstcode, apply_ite Search.firsttc,
    apply_ite Search.firstlab, ite_self]

/-- Recording a generator preserves the first-path reference. -/
theorem admit_reference (st : Search n) : (admit st).reference = st.reference := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

/-- Pruning past a leaf preserves the first-path reference. -/
theorem pruneReturn_reference (level : Nat) (st : Search n) :
    (pruneReturn level st).2.reference = st.reference := by
  unfold pruneReturn
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite Search.reference, pushAuto_reference, ite_self]

/-- Off-path leaf processing never replaces the first-path reference. -/
theorem leafExit_reference (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.reference = st.reference := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact admit_reference _
    | exact pruneReturn_reference level _

/-- The engine's off-path operations preserve all first-path reference fields. -/
theorem referencePolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.ReferencePolicy ctx inf tcLevel (Search.reference (n := n)) where
  visit := fun _ _ _ => rfl
  compare := by
    intro level code st
    change (compareCodes level code st).reference = st.reference
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, Search.reference,
      apply_ite Search.firstcode, apply_ite Search.firsttc, apply_ite Search.firstlab, ite_self]
  target := by
    intro level numcells st
    change (chooseTarget false ctx tcLevel level numcells st).2.2.2.reference = st.reference
    rw [chooseTarget_fields]
    rfl
  classify := classify_reference ctx
  leaf := leafExit_reference
  cheap := by
    intro first level st
    change (cheapCheck first level st).reference = st.reference
    unfold cheapCheck
    split <;> rfl
  child := by
    intro first level tc tv st
    cases first <;> rfl
  leave := fun _ _ => rfl
  recover := by
    intro level st
    change (Nauty.recover inf level st).reference = st.reference
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, Search.reference,
      apply_ite Search.firstcode, apply_ite Search.firsttc, apply_ite Search.firstlab, ite_self]
  afterSweep := by
    intro first level size index st
    change (afterSweep first level size index st).reference = st.reference
    unfold afterSweep
    split <;> rfl

/-- Off-path search preserves the saved first-path codes, targets, and leaf. -/
theorem node_reference (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (st : Search n) :
    (node false ctx inf tcLevel fuel level numcells st).2.reference = st.reference := by
  rw [node_eq_generic]
  exact Generic.node_reference (referencePolicy ctx inf tcLevel) fuel level numcells st

/-- A sweep past its first child preserves the saved first-path reference. -/
theorem sweep_reference (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : Search n)
    (hpast : Generic.Past first tv1 cursor) :
    (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.reference =
      st.reference := by
  rw [sweep_eq_generic]
  exact Generic.sweep_reference (referencePolicy ctx inf tcLevel) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast

end Hex.GraphIso.Nauty
