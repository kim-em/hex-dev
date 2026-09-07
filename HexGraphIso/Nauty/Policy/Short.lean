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

/-- A short return carries a property established by its emitting leaf. -/
def shortContract (P : Nat → σ → Prop) : Contract σ n where
  nodePre _ _ _ _ _ := True
  nodePost _ _ _ _ _ result := ∀ target, result.1 = .unwind target true → P target result.2
  sweepPre _ _ _ _ _ _ _ _ _ _ _ := True
  sweepPost _ _ _ _ _ _ _ _ _ _ _ result :=
    ∀ target, result.1 = .unwind target true → P target result.2.2

/-- Only leaf emission and cleanup along an unconsumed return must
preserve the property. A receiving loop may consume it and resume. -/
structure ShortPolicy (P : Nat → σ → Prop) : Prop where
  leaf : ∀ leaf level st target,
    (Policy.leafExit (n := n) leaf level st).1 = .unwind target true →
      P target (Policy.leafExit (n := n) leaf level st).2
  afterFirst : ∀ level tv target st, P target st →
    P target (Policy.afterChildFirst (n := n) level tv st)
  leave : ∀ tv target st, P target st → P target (Policy.leaveChild (n := n) tv st)

variable {P : Nat → σ → Prop}

/-- Resuming a sweep obtains any new short return from its continuation. -/
theorem short_resume {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (shortContract (n := n) P).sweepValid fuel cfuel next)
    (inf : Nat) (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (st : σ) :
    ∀ target, (resume inf next first level numcells tc tv1 tv cell index st).1 =
      .unwind target true →
      P target (resume inf next first level numcells tc tv1 tv cell index st).2.2 := by
  unfold resume
  split <;> exact hnext _ _ _ _ _ _ _ _ _ trivial

/-- An intermediate loop transports an unconsumed short return. -/
theorem short_advance {fuel cfuel : Nat} {next : SweepFn σ n}
    (hnext : (shortContract (n := n) P).sweepValid fuel cfuel next)
    (inf : Nat) (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (st : σ) (exit : Exit)
    (hout : ∀ target, exit = .unwind target true → P target st) :
    ∀ target, (advance inf next first level numcells tc tv1 tv cell index st exit).1 =
      .unwind target true →
      P target (advance inf next first level numcells tc tv1 tv cell index st exit).2.2 := by
  unfold advance
  cases exit with
  | fuel => simp
  | done => exact short_resume hnext inf first level numcells tc tv1 tv index cell st
  | unwind target short =>
    simp only [Id.run_pure, apply_ite Id.run]
    split
    · exact hout
    · cases short <;>
        exact short_resume hnext inf first level numcells tc tv1 tv index _ st

/-- A node can emit a short return only at a leaf or through its sweep. -/
theorem short_node (h : ShortPolicy (n := n) P) {fuel : Nat} {next : SweepFn σ n}
    (hnext : (shortContract (n := n) P).sweepValid fuel (n + 1) next)
    (ctx : Ctx n) (tcLevel : Nat) (first : Bool) (level numcells : Nat) (st : σ) :
    ∀ target, (nodeStep ctx tcLevel next first level numcells st).1 = .unwind target true →
      P target (nodeStep ctx tcLevel next first level numcells st).2 := by
  unfold nodeStep
  generalize Policy.visit ctx level numcells st = visited
  obtain ⟨nc, code, refined⟩ := visited
  dsimp only
  generalize Policy.chooseTarget first ctx tcLevel level nc
    (if first then Policy.recordFirst (n := n) level code refined
      else Policy.compareCodes (n := n) level code refined) = targeted
  obtain ⟨tc, cell, size, prepared⟩ := targeted
  have finish : ∀ ready,
      let tv := cell.nextElem none
      let result := next first level nc tc.toNat (tv.getD 0) tv cell 0
        (Policy.cheapCheck (n := n) first level ready)
      ∀ target, (Id.run (match result.1 with
        | .done => pure (Exit.unwind (level - 1) false,
            Policy.afterSweep (n := n) first level size result.2.1 result.2.2)
        | _ => pure (result.1, result.2.2))).1 = .unwind target true →
        P target (Id.run (match result.1 with
        | .done => pure (Exit.unwind (level - 1) false,
            Policy.afterSweep (n := n) first level size result.2.1 result.2.2)
        | _ => pure (result.1, result.2.2))).2 := by
    intro ready
    dsimp only
    have hn := hnext first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) first level ready) trivial
    change ∀ target, _ = Exit.unwind target true → P target _ at hn
    generalize next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) first level ready) = result at hn ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | done => simp
    | unwind => exact hn
    | fuel => simp
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run]
    split
    · simp
    · exact finish prepared
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    generalize Policy.classify ctx level nc prepared = classified
    obtain ⟨leaf, classified⟩ := classified
    have hl := h.leaf leaf level classified
    generalize Policy.leafExit (n := n) leaf level classified = result at hl ⊢
    obtain ⟨exit, out⟩ := result
    cases exit with
    | done => exact finish out
    | unwind => exact hl
    | fuel => simp

/-- Cleanup preserves the emitting leaf's property before the loop
either transports the return or resumes its continuation. -/
theorem short_sweep (h : ShortPolicy (n := n) P) {fuel cfuel : Nat}
    {descend : NodeFn σ} {next : SweepFn σ n}
    (hdescend : (shortContract (n := n) P).nodeValid fuel descend)
    (hnext : (shortContract (n := n) P).sweepValid fuel cfuel next)
    (inf : Nat) (first : Bool) (level numcells tc tv1 tv index : Nat)
    (cell : VSet n) (st : σ) :
    ∀ target, (sweepStep inf descend next first level numcells tc tv1 tv cell index st).1 =
      .unwind target true →
      P target (sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2 := by
  unfold sweepStep
  dsimp only
  split
  · have hd := hdescend (first && tv == tv1) (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) trivial
    change ∀ target, _ = Exit.unwind target true → P target _ at hd
    generalize descend (first && tv == tv1) (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = result at hd ⊢
    obtain ⟨exit, out⟩ := result
    split
    · apply short_advance hnext
      intro target he
      exact h.leave _ _ _ (h.afterFirst _ _ _ _ (hd target he))
    · apply short_advance hnext
      intro target he
      exact h.leave _ _ _ (hd target he)
  · exact hnext _ _ _ _ _ _ _ _ _ trivial

/-- The leaf rules instantiate the common recursion's contract. -/
theorem ShortPolicy.sound (h : ShortPolicy (n := n) P) (ctx : Ctx n) (inf tcLevel : Nat) :
    SoundPolicy ctx inf tcLevel (shortContract (n := n) P) where
  node_zero := by intros; simp [shortContract]
  node_step := by
    intro fuel next hn first level numcells st _
    exact short_node h hn ctx tcLevel first level numcells st
  sweep_none := by intros; simp [shortContract]
  sweep_zero := by intros; simp [shortContract]
  sweep_step := by
    intro fuel cfuel descend next hd hn first level numcells tc tv1 tv cell index st _
    exact short_sweep h hd hn inf first level numcells tc tv1 tv index cell st

/-- Every short return carries a property of its emitting leaf. -/
theorem node_short (h : ShortPolicy (n := n) P) (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel level numcells : Nat) (st : σ) :
    ∀ target, (node first ctx inf tcLevel fuel level numcells st).1 = .unwind target true →
      P target (node first ctx inf tcLevel fuel level numcells st).2 :=
  node_sound (h.sound ctx inf tcLevel) first fuel level numcells st trivial

/-- An unconsumed short return retains its emitting leaf's property
through any number of intermediate sweeps. -/
theorem sweep_short (h : ShortPolicy (n := n) P) (first : Bool) (ctx : Ctx n)
    (inf tcLevel fuel cfuel level numcells tc tv1 : Nat) (cursor : Option Nat)
    (cell : VSet n) (index : Nat) (st : σ) :
    ∀ target, (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).1 =
      .unwind target true →
      P target (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 :=
  sweep_sound (h.sound ctx inf tcLevel) first fuel cfuel level numcells tc tv1 cursor cell index st trivial

end Hex.GraphIso.Nauty.Generic
