/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Search.Generic
public import HexGraphIso.Nauty.Invariant.Domination
public import HexGraphIso.Nauty.Model.Autom
import all HexGraphIso.Nauty.Search.Generic

public section

/-! A policy that visits every target-cell position. Parent partitions
are saved explicitly so that sibling traversal is independent of the
labelling left by the previous child. -/

namespace Hex.GraphIso.Nauty.Generic.Trivial

variable {n : Nat}

/-- A partition, its path codes, and the key it would have as a leaf. -/
structure Frame (n : Nat) where
  partition : RefineSt n
  codes : List Nat
  candidate : Key n

/-- The exhaustive traversal's current frame, saved parents, and incumbent. -/
structure State (n : Nat) where
  frame : Frame n
  parents : List (Frame n)
  best : Option (Key n)

/-- Refine the current partition and append its code to the current path. -/
@[expose] def visit (ctx : Ctx n) (level numcells : Nat) (st : State n) : State n :=
  let p := st.frame.partition
  let r := refine ctx level p.lab p.ptn p.active numcells
  let codes := st.frame.codes ++ [r.longcode]
  { st with frame := ⟨r, codes, ⟨codes ++ [codeSentinel], leafRows ctx r.lab⟩⟩ }

/-- The target positions, enumerated in increasing offset order. -/
@[expose] def positions (len : Nat) : VSet n := VSet.ofList (List.range len)

/-- Individualize an offset of the current target cell, retaining its parent frame. -/
@[expose] def child (level tc offset : Nat) (st : State n) : State n :=
  let p := st.frame.partition
  let b := breakout n p.lab p.ptn (level + 1) tc p.lab[tc + offset]!
  { st with
    parents := st.frame :: st.parents
    frame := { st.frame with partition :=
      { lab := b.1, ptn := b.2.1, active := b.2.2, numcells := p.numcells + 1,
        hint := 0, maxpos := 0, longcode := 0 } } }

/-- Restore the saved parent while retaining the child's incumbent. -/
@[expose] def recover (st : State n) : State n :=
  match st.parents with
  | [] => st
  | frame :: parents => { st with frame, parents }

/-- Install the current leaf into the incumbent. -/
@[expose] def install (st : State n) : State n :=
  { st with best := some (incMax st.best st.frame.candidate) }

/-- The exhaustive policy uses the specification's target selector and
never removes a target position or returns past its immediate parent. -/
instance policy : Policy (State n) n where
  visit ctx level numcells st :=
    let out := visit ctx level numcells st
    (out.frame.partition.numcells, out.frame.partition.longcode, out)
  recordFirst _ _ st := st
  compareCodes _ _ st := st
  chooseTarget _ ctx tcLevel level _ st :=
    let p := st.frame.partition
    let t := specMaketargetcell ctx p.lab p.ptn level tcLevel
    (Int.ofNat t.1, positions t.2.2, t.2.2, st)
  firstterminal _ st := install st
  classify _ level _ st :=
    (if discreteAt st.frame.partition.ptn level n then .better 0 else .internal, st)
  leafExit leaf level st :=
    if leaf == .internal then (.done, st) else (.unwind (level - 1) false, install st)
  cheapCheck _ _ st := st
  child _ level tc offset st := child level tc offset st
  afterChildFirst _ _ st := st
  leaveChild _ st := st
  orbit _ v := v
  shortprune cell _ := cell
  longprune cell _ := cell
  recover _ _ st := recover st
  afterSweep _ _ _ _ st := st

/-- A valid offset set has precisely its requested interval as members. -/
theorem mem_positions {len : Nat} (hlen : len ≤ n) (v : Nat) :
    (positions len : VSet n).mem v = decide (v < len) := by
  simp only [positions, VSet.mem_ofList, List.contains_eq_mem, List.mem_range]
  by_cases hv : v < len
  · simp [hv, show v < n by omega]
  · simp [hv]

/-- The next offset is the scan start whenever it is still within the target. -/
theorem next_positions {len : Nat} (hlen : len ≤ n) (cursor : Option Nat) :
    (positions len : VSet n).nextElem cursor =
      if VSet.scanStart cursor < len then some (VSet.scanStart cursor) else none := by
  split
  · rename_i hlt
    apply VSet.nextElem_eq_some_iff.mpr
    exact ⟨by simp [mem_positions hlen, hlt], Nat.le_refl _, fun _ hlo hhi => by omega⟩
  · rename_i hge
    apply VSet.nextElem_eq_none_iff.mpr
    intro v hv
    simp only [mem_positions hlen]
    exact decide_eq_false (by omega)

/-- Completing a child restores exactly its parent frame and new incumbent. -/
theorem recover_child (ctx : Ctx n) (level tc offset : Nat) (st : State n)
    (best : Option (Key n)) :
    recover { visit ctx (level + 1) (st.frame.partition.numcells + 1)
      (child level tc offset st) with best } = { st with best } := rfl

/-- Sufficient depth for the exhaustive refinement tree. The interval
bounds ensure every target offset is representable by the policy's bitset. -/
inductive Complete (ctx : Ctx n) (tcLevel : Nat) : Nat → Nat → RefineSt n → Prop where
  | leaf {fuel level : Nat} {p : RefineSt n}
      (discrete : discreteAt (refine ctx level p.lab p.ptn p.active p.numcells).ptn level n = true) :
      Complete ctx tcLevel (fuel + 1) level p
  | branch {fuel level : Nat} {p : RefineSt n}
      (nondiscrete : discreteAt (refine ctx level p.lab p.ptn p.active p.numcells).ptn level n = false)
      (positive : let r := refine ctx level p.lab p.ptn p.active p.numcells
        0 < (specMaketargetcell ctx r.lab r.ptn level tcLevel).2.2)
      (bounded : let r := refine ctx level p.lab p.ptn p.active p.numcells
        (specMaketargetcell ctx r.lab r.ptn level tcLevel).2.2 ≤ n)
      (children : let r := refine ctx level p.lab p.ptn p.active p.numcells
        let t := specMaketargetcell ctx r.lab r.ptn level tcLevel
        ∀ o, o < t.2.2 → Complete ctx tcLevel fuel (level + 1)
          (child level t.1 o ⟨⟨r, [], default⟩, [], none⟩).frame.partition) :
      Complete ctx tcLevel (fuel + 1) level p

end Hex.GraphIso.Nauty.Generic.Trivial
