/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.Leftmost
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Every off-path operation preserves the canonical row cache; a better
verdict supplies the candidate prefix required by installation. -/
theorem storePolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.StablePolicy ctx inf tcLevel
      (fun st : Search n => CanongInv ctx st.canong st.canonlab st.samerows)
      (fun _ => True)
      (fun leaf st => ∀ sr, leaf = .better sr → CanongInv ctx st.canong st.lab sr) where
  code := fun _ _ _ => trivial
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change CanongInv ctx (compareCodes level code st).canong (compareCodes level code st).canonlab
      (compareCodes level code st).samerows
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.canong,
      apply_ite Search.canonlab, apply_ite Search.samerows, ite_self]
    exact h
  target := by
    intro level numcells st h
    change CanongInv ctx (chooseTarget false ctx tcLevel level numcells st).2.2.2.canong
      (chooseTarget false ctx tcLevel level numcells st).2.2.2.canonlab
      (chooseTarget false ctx tcLevel level numcells st).2.2.2.samerows
    rw [chooseTarget_fields]
    exact h
  classify := fun _ _ _ h => classify_store h
  leaf := fun _ _ _ hnew h => leafExit_store ⟨h, hnew⟩
  cheap := by
    intro first level st h
    change CanongInv ctx (cheapCheck first level st).canong (cheapCheck first level st).canonlab
      (cheapCheck first level st).samerows
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    change CanongInv ctx (recoverLevels level (recoverPtn inf level st)).canong
      (recoverLevels level (recoverPtn inf level st)).canonlab
      (recoverLevels level (recoverPtn inf level st)).samerows
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.canong,
      apply_ite Search.canonlab, apply_ite Search.samerows, ite_self]
    exact h
  afterSweep := by
    intro first level size index st h
    change CanongInv ctx (afterSweep first level size index st).canong
      (afterSweep first level size index st).canonlab (afterSweep first level size index st).samerows
    unfold afterSweep
    split <;> exact h

/-- An off-path engine call preserves the canonical row-store invariant. -/
theorem node_store {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat} {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) :
    let out := (node false ctx inf tcLevel fuel level numcells st).2
    CanongInv ctx out.canong out.canonlab out.samerows := by
  rw [node_eq_generic]
  exact Generic.node_stable (storePolicy ctx inf tcLevel) fuel level numcells st h

/-- Later siblings preserve the canonical row-store invariant through every exit. -/
theorem sweep_store {ctx : Ctx n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index : Nat}
    {cursor : Option Nat} {cell : VSet n} {st : Search n}
    (h : CanongInv ctx st.canong st.canonlab st.samerows) (hpast : Generic.Past first tv1 cursor) :
    let out := (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2
    CanongInv ctx out.canong out.canonlab out.samerows := by
  rw [sweep_eq_generic]
  exact Generic.sweep_stable (storePolicy ctx inf tcLevel) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast h

/-- Before its first leaf the engine has not changed the canonical row array. -/
theorem firstPath_canong {ctx : Ctx n} {tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf) :
    leaf.canong = st.canong := by
  have hprepare : ∀ level numcells (st : Search n),
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2.canong = st.canong := by
    intro level numcells st
    unfold Generic.prepareFirst
    change (chooseTarget true ctx tcLevel level _ _).2.2.2.canong = _
    rw [chooseFirst_fields]
    rfl
  induction hpath with
  | leaf fuel level numcells st hdisc => exact hprepare level numcells st
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    rw [ih]
    change (cheapCheck true level
      (Generic.prepareFirst ctx tcLevel level numcells st).2.2.2.2).canong = _
    unfold cheapCheck
    split <;> exact hprepare level numcells st

/-- A successful first-path call initializes and preserves the canonical row cache. -/
theorem firstPath_store {ctx : Ctx n} {inf tcLevel fuel level numcells last : Nat}
    {st leaf : Search n}
    (hpath : Generic.FirstPath ctx tcLevel fuel level numcells st last leaf)
    (hsize : st.canong.size = n) :
    let out := (node true ctx inf tcLevel fuel level numcells st).2
    CanongInv ctx out.canong out.canonlab out.samerows := by
  rw [node_eq_generic]
  apply hpath.stable (storePolicy ctx inf tcLevel) (fun _ _ _ h => h)
  change CanongInv ctx leaf.canong leaf.lab 0
  apply canongInv_zero
  rw [firstPath_canong hpath, hsize]

/-- The complete engine run has a valid canonical row cache. -/
theorem runState_store {k : Nat} (G : Colored n k) :
    let out := (runState n (rowsOf G) (initialPartition G).1 (initialPartition G).2).2
    CanongInv { g := rowsOf G } out.canong out.canonlab out.samerows := by
  unfold runState
  split
  · apply canongInv_zero
    simp [initial]
  · rename_i hne
    have hn0 : 0 < n := by
      have : n ≠ 0 := by simpa using hne
      omega
    obtain ⟨last, leaf, hpath⟩ := initial_path G hn0
    exact firstPath_store hpath (by simp [initial])

end Hex.GraphIso.Nauty.Engine
