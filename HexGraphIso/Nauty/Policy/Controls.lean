/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.Instance
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Admitting a generator retains the first-path ancestor. -/
theorem admit_gca {κ : Type} (st : SearchState n κ) : (admit st).gcaFirst = st.gcaFirst := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

private theorem pruneReturn_gca {κ : Type} (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.gcaFirst = st.gcaFirst := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Leaf actions preserve the ancestor shared with the first path. -/
theorem leafExit_gca {κ : Type} (leaf : Leaf) (level : Nat) (st : SearchState n κ) :
    (leafExit leaf level st).2.gcaFirst = st.gcaFirst := by
  cases leaf <;> unfold leafExit
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals first
    | rfl
    | exact admit_gca _
    | exact pruneReturn_gca level _

/-- Admitting a generator retains the canonical ancestor. -/
theorem admit_canon {κ : Type} (st : SearchState n κ) : (admit st).gcaCanon = st.gcaCanon := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

/-- Admitting a generator retains the canonical labelling. -/
theorem admit_ref {κ : Type} (st : SearchState n κ) : (admit st).canonlab = st.canonlab := by
  unfold admit pushAuto
  simp only [Id.run_pure]
  split <;> rfl

/-- A canonical automorphism return retains its reference labelling. -/
theorem autoCanon_ref {κ : Type} (level : Nat) (st : SearchState n κ) :
    (leafExit .autoCanon level st).2.canonlab = st.canonlab := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals exact admit_ref _

/-- A canonical automorphism return retains its canonical ancestor. -/
theorem autoCanon_ancestor {κ : Type} (level : Nat) (st : SearchState n κ) :
    (leafExit .autoCanon level st).2.gcaCanon = st.gcaCanon := by
  unfold leafExit
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals exact admit_canon _

/-- The shared prune tail retains the canonical ancestor. -/
theorem pruneReturn_canon {κ : Type} (level : Nat) (st : SearchState n κ) :
    (pruneReturn level st).2.gcaCanon = st.gcaCanon := by
  unfold pruneReturn pushAuto
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  repeat' split
  all_goals rfl

/-- Parent recovery retains the stored canonical labelling. -/
theorem recover_ref {κ : Type} (inf level : Nat) (st : SearchState n κ) :
    (Nauty.recover inf level st).canonlab = st.canonlab := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canonlab]
  repeat' split
  all_goals rfl

/-- Code comparison retains the ancestor of the canonical path. -/
theorem compare_canon {κ : Type} (level code : Nat) (st : SearchState n κ) :
    (compareCodes level code st).gcaCanon = st.gcaCanon := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaCanon, ite_self]

/-- Target selection retains the ancestor of the canonical path. -/
theorem target_canon (first : Bool) (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) :
    (chooseTarget first ctx tcLevel level numcells st).2.2.2.gcaCanon = st.gcaCanon := by
  cases first <;> first | rw [chooseTarget_fields] | rw [chooseFirst_fields]

/-- Classification retains the ancestor of the canonical path. -/
theorem classify_canon (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.gcaCanon = st.gcaCanon := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.gcaCanon, ite_self]

/-- Testing a small cell retains the ancestor of the canonical path. -/
theorem cheap_canon {κ : Type} (first : Bool) (level : Nat) (st : SearchState n κ) :
    (cheapCheck first level st).gcaCanon = st.gcaCanon := by
  unfold cheapCheck
  split <;> rfl

/-- Recovery clamps the canonical ancestor to the receiving sweep. -/
theorem recover_canon {κ : Type} {inf : Nat} (level : Nat) (st : SearchState n κ) :
    (Nauty.recover inf level st).gcaCanon = min level st.gcaCanon := by
  unfold Nauty.recover recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaCanon]
  repeat' split
  all_goals omega

/-- The recovered canonical ancestor is no deeper than its sweep. -/
theorem recover_canon_le {κ : Type} {inf : Nat} (level : Nat) (st : SearchState n κ) :
    (Nauty.recover inf level st).gcaCanon ≤ level := by
  rw [recover_canon]
  exact Nat.min_le_left _ _

/-- Outside the first descent the first-path ancestor is a fixed frame. -/
theorem gcaPolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.ReferencePolicy ctx inf tcLevel (fun st : Search n => st.gcaFirst) where
  visit := fun _ _ _ => rfl
  compare := by
    intro level code st
    change (compareCodes level code st).gcaFirst = st.gcaFirst
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst, ite_self]
  target := by
    intro level numcells st
    change (chooseTarget false ctx tcLevel level numcells st).2.2.2.gcaFirst = st.gcaFirst
    rw [chooseTarget_fields]
  classify := by
    intro level numcells st
    change (classify ctx level numcells st).2.gcaFirst = st.gcaFirst
    unfold classify
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
      apply_ite SearchState.gcaFirst, ite_self]
  leaf := leafExit_gca
  cheap := by
    intro first level st
    change (cheapCheck first level st).gcaFirst = st.gcaFirst
    unfold cheapCheck
    split <;> rfl
  child := by intro first level tc tv st; cases first <;> rfl
  leave := fun _ _ => rfl
  recover := by
    intro level st
    change (Nauty.recover inf level st).gcaFirst = st.gcaFirst
    unfold Nauty.recover recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst, ite_self]
  afterSweep := by
    intro first level size index st
    change (afterSweep first level size index st).gcaFirst = st.gcaFirst
    unfold afterSweep
    split <;> rfl

/-- An off-path node retains its first-path ancestor throughout its return. -/
theorem node_gca (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n) :
    (node false ctx inf tcLevel fuel level numcells st).2.gcaFirst = st.gcaFirst := by
  rw [node_eq_generic]
  exact Generic.node_reference (gcaPolicy ctx inf tcLevel) fuel level numcells st

/-- Once past the first child, a sweep retains its first-path ancestor. -/
theorem sweep_gca (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : Search n)
    (hpast : Generic.Past first tv1 cursor) :
    (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.gcaFirst =
      st.gcaFirst := by
  rw [sweep_eq_generic]
  exact Generic.sweep_reference (gcaPolicy ctx inf tcLevel) first fuel cfuel level numcells tc tv1
    index cursor cell st hpast

end Hex.GraphIso.Nauty
