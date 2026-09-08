/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ : Type} [Policy σ n]

/-- A sweep consumes every unwind that does not leave its level. -/
def exitContract : Contract σ n where
  nodePre _ _ _ _ _ := True
  nodePost _ _ _ _ _ _ := True
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost _ _ _ level _ _ _ _ _ _ _ result :=
    ∀ target short, result.1 = .unwind target short → target < level

/-- Resuming preserves the remaining sweep's bound on its exit. -/
theorem bound_resume {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (exitContract (σ := σ) (n := n)).sweepValid fuel cfuel next)
    (inf : Nat) (first : Bool) (level numcells tc tv1 tv : Nat)
    (cell : VSet n) (index : Nat) (st : σ) :
    ∀ target short, (resume inf next first level numcells tc tv1 tv cell index st).1 =
      .unwind target short → target < level := by
  unfold resume
  split <;> exact hnext _ _ _ _ _ _ _ _ _ trivial

/-- Only an unwind below this level can pass through a receiving sweep. -/
theorem bound_advance {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (exitContract (σ := σ) (n := n)).sweepValid fuel cfuel next)
    (inf : Nat) (first : Bool) (level numcells tc tv1 tv : Nat)
    (cell : VSet n) (index : Nat) (st : σ) (exit : Exit) :
    ∀ target short, (advance inf next first level numcells tc tv1 tv cell index st exit).1 =
      .unwind target short → target < level := by
  unfold advance
  cases exit with
  | fuel => simp
  | done => exact bound_resume hnext inf first level numcells tc tv1 tv cell index st
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run]
    split
    · intro t s he
      cases he
      assumption
    · cases short <;>
        exact bound_resume hnext inf first level numcells tc tv1 tv _ index st

/-- A positive node returns below its level when its local leaf action does.
The sweep bound is independent of the state passed to the continuation. -/
theorem bound_node {fuel : Nat} {next : SweepFn σ n}
    (hnext : (exitContract (σ := σ) (n := n)).sweepValid fuel (n + 1) next)
    (ctx : Ctx n) (tcLevel : Nat) (first : Bool) (level numcells : Nat) (st : σ)
    (hlevel : 1 ≤ level)
    (hleaf : first = false →
      let r := Policy.visit ctx level numcells st
      let p := Policy.chooseTarget first ctx tcLevel level r.1
        (if first then Policy.recordFirst (n := n) level r.2.1 r.2.2
          else Policy.compareCodes (n := n) level r.2.1 r.2.2)
      let c := Policy.classify ctx level r.1 p.2.2.2
      ∀ target short, (Policy.leafExit (n := n) c.1 level c.2).1 = .unwind target short →
        target < level) :
    ∀ target short, (nodeStep ctx tcLevel next first level numcells st).1 =
      .unwind target short → target < level := by
  unfold nodeStep
  generalize Policy.visit ctx level numcells st = visited at hleaf ⊢
  obtain ⟨nc, code, refined⟩ := visited
  dsimp only at hleaf ⊢
  generalize Policy.chooseTarget first ctx tcLevel level nc
    (if first then Policy.recordFirst (n := n) level code refined
      else Policy.compareCodes (n := n) level code refined) = targeted at hleaf ⊢
  obtain ⟨tc, cell, size, prepared⟩ := targeted
  have finish : ∀ ready,
      let tv := cell.nextElem none
      let result := next first level nc tc.toNat (tv.getD 0) tv cell 0
        (Policy.cheapCheck (n := n) first level ready)
      ∀ target short, (Id.run (match result.1 with
        | .done => pure (Exit.unwind (level - 1) false,
            Policy.afterSweep (n := n) first level size result.2.1 result.2.2)
        | _ => pure (result.1, result.2.2))).1 = .unwind target short → target < level := by
    intro ready
    dsimp only
    have hn := hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) first level ready) trivial
    change ∀ target short, _ = Exit.unwind target short → target < level at hn
    generalize next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) first level ready) = result at hn ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | done => intro target short he; cases he; omega
    | unwind => exact hn
    | fuel => simp
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run]
    split
    · intro target short he; cases he; omega
    · exact finish prepared
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hl := hleaf rfl
    dsimp only at hl
    generalize Policy.classify ctx level nc prepared = classified at hl ⊢
    obtain ⟨leaf, classified⟩ := classified
    generalize Policy.leafExit (n := n) leaf level classified = result at hl ⊢
    obtain ⟨exit, out⟩ := result
    cases exit with
    | done => exact finish out
    | unwind => exact hl
    | fuel => simp

/-- The unwind bound depends only on the generic sweep's control flow. -/
theorem exitPolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    SoundPolicy (σ := σ) ctx inf tcLevel exitContract where
  node_zero := by intros; trivial
  node_step := by intros; trivial
  sweep_none := by intros; simp [exitContract]
  sweep_zero := by intros; simp [exitContract]
  sweep_step := by
    intro fuel cfuel descend next _ hn first level numcells tc tv1 tv cell index st _
    change ∀ target short, _ = Exit.unwind target short → target < level
    unfold sweepStep
    dsimp only
    split
    · generalize descend (first && tv == tv1) (level + 1) (numcells + 1)
        (Policy.child (n := n) first level tc tv st) = result
      obtain ⟨exit, out⟩ := result
      split <;> exact bound_advance hn inf first level numcells tc tv1 tv cell index _ exit
    · exact hn _ _ _ _ _ _ _ _ _ trivial

/-- Every sweep returns an unwind strictly below its own level, regardless
of the child policies, input state, or recursion bounds. -/
theorem sweep_bound (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : σ) :
    ∀ target short,
      (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 =
        .unwind target short → target < level :=
  sweep_sound (exitPolicy ctx inf tcLevel) first fuel cfuel level numcells tc tv1
    cursor cell index st trivial

end Hex.GraphIso.Nauty.Generic
