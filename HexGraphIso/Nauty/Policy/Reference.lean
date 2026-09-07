/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Policy.Sound
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.VSet.Basic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ α : Type}

/-- A sweep is strictly past its first child, or is entirely off the first path. -/
def Past (first : Bool) (tv1 : Nat) (cursor : Option Nat) : Prop :=
  first = true → ∀ v, cursor = some v → tv1 < v

/-- Every later bitset cursor remains past the first child. -/
theorem Past.next {first : Bool} {tv1 tv : Nat} {cell : VSet n}
    (h : first = true → tv1 < tv) : Past first tv1 (cell.nextElem (some tv)) := by
  intro hf v hv
  have hnext := (VSet.nextElem_eq_some_iff.mp hv).2.1
  change tv + 1 ≤ v at hnext
  have := h hf
  omega

/-- The first-path fields remain fixed on off-path calls and later siblings. -/
def referenceContract (n : Nat) (project : σ → α) : Contract σ n where
  nodePre _ first _ _ _ := first = false
  nodePost _ _ _ _ st result := project result.2 = project st
  sweepPre _ _ first _ _ _ tv1 cursor _ _ _ := Past first tv1 cursor
  sweepPost _ _ _ _ _ _ _ _ _ _ st result := project result.2.2 = project st

variable [Policy σ n]

/-- Local operations outside the first descent preserve a projection
of the policy state, such as the first labelling, codes, and target array. -/
structure ReferencePolicy (ctx : Ctx n) (inf tcLevel : Nat) (project : σ → α) : Prop where
  visit : ∀ level numcells st, project (Policy.visit ctx level numcells st).2.2 = project st
  compare : ∀ level code st, project (Policy.compareCodes (n := n) level code st) = project st
  target : ∀ level numcells st,
    project (Policy.chooseTarget false ctx tcLevel level numcells st).2.2.2 = project st
  classify : ∀ level numcells st, project (Policy.classify ctx level numcells st).2 = project st
  leaf : ∀ leaf level st, project (Policy.leafExit (n := n) leaf level st).2 = project st
  cheap : ∀ first level st, project (Policy.cheapCheck (n := n) first level st) = project st
  child : ∀ first level tc tv st, project (Policy.child (n := n) first level tc tv st) = project st
  leave : ∀ tv st, project (Policy.leaveChild (n := n) tv st) = project st
  recover : ∀ level st, project (Policy.recover (n := n) inf level st) = project st
  afterSweep : ∀ first level size index st,
    project (Policy.afterSweep (n := n) first level size index st) = project st

variable {ctx : Ctx n} {inf tcLevel : Nat} {project : σ → α}

/-- An off-path node cannot change the first-path projection. -/
theorem ReferencePolicy.node_step (h : ReferencePolicy ctx inf tcLevel project)
    {fuel : Nat} {next : SweepFn σ n}
    (hnext : (referenceContract n project).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : σ) :
    project (nodeStep ctx tcLevel next false level numcells st).2 = project st := by
  have hv := h.visit level numcells st
  unfold nodeStep
  generalize hr : Policy.visit ctx level numcells st = r at hv ⊢
  obtain ⟨nc, code, refined⟩ := r
  simp only [Bool.false_eq_true, ite_false]
  let compared := Policy.compareCodes (n := n) level code refined
  have hcomp : project compared = project st := (h.compare level code refined).trans hv
  have ht := h.target level nc compared
  generalize htval : Policy.chooseTarget false ctx tcLevel level nc compared = t at ht ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  have hcl := h.classify level nc targeted
  generalize hcval : Policy.classify ctx level nc targeted = c at hcl ⊢
  obtain ⟨leaf, classified⟩ := c
  have hle := h.leaf leaf level classified
  generalize hlval : Policy.leafExit (n := n) leaf level classified = result at hle ⊢
  obtain ⟨exit, out⟩ := result
  have hproject : project out = project st := hle.trans (hcl.trans (ht.trans hcomp))
  cases exit with
  | fuel => exact hproject
  | unwind => exact hproject
  | done =>
    have hc := h.cheap false level out
    have hn := hnext false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) false level out)
      (by intro hf; cases hf)
    generalize hsval : next false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) false level out) = s at hn ⊢
    obtain ⟨exit, index, result⟩ := s
    cases exit with
    | fuel => exact hn.trans (hc.trans hproject)
    | unwind => exact hn.trans (hc.trans hproject)
    | done => exact (h.afterSweep false level size index result).trans (hn.trans (hc.trans hproject))

/-- Once past the first child, all later recursive calls are off-path. -/
theorem ReferencePolicy.sweep_step (h : ReferencePolicy ctx inf tcLevel project)
    {fuel cfuel : Nat} {descend : NodeFn σ} {next : SweepFn σ n}
    (hdescend : (referenceContract n project).nodeValid fuel descend)
    (hnext : (referenceContract n project).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : σ)
    (hpast : Past first tv1 (some tv)) :
    project (sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2 =
      project st := by
  have htv : first = true → tv1 < tv := fun hf => hpast hf tv rfl
  have hflag : (first && tv == tv1) = false := by
    cases first with
    | false => rfl
    | true =>
      have := htv rfl
      simp only [Bool.true_and, beq_eq_false_iff_ne]
      omega
  have hcontinue : ∀ cell out, project out = project st →
      project (next first level numcells tc tv1 (cell.nextElem (some tv)) cell
        (if first && Policy.orbit (n := n) (Policy.recover (n := n) inf level out) tv == tv1
          then index + 1 else index)
        (Policy.recover (n := n) inf level out)).2.2 = project st := by
    intro cell out heq
    exact (hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ _
      (Past.next htv)).trans ((h.recover level out).trans heq)
  have hd := hdescend false (level + 1) (numcells + 1)
    (Policy.child (n := n) first level tc tv st) rfl
  have hchild := h.child first level tc tv st
  unfold sweepStep
  simp only [hflag, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize hdval : descend false (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = result at hd ⊢
    obtain ⟨exit, out⟩ := result
    have heq := (h.leave tv out).trans (hd.trans hchild)
    cases exit with
    | fuel => exact heq
    | done =>
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split <;> exact hcontinue _ _ heq
    | unwind target short =>
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact heq
      · cases short <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        all_goals split <;> exact hcontinue _ _ heq
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st (Past.next htv)

/-- Reference preservation is an instance of the generic recursion contract. -/
theorem ReferencePolicy.sound (h : ReferencePolicy ctx inf tcLevel project) :
    SoundPolicy ctx inf tcLevel (referenceContract n project) where
  node_zero := fun _ _ _ _ _ => rfl
  node_step := by
    intro fuel next hnext first level numcells st hin
    subst first
    exact h.node_step hnext level numcells st
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ _ => rfl
  sweep_step := fun _ _ _ _ hdescend hnext first level numcells tc tv1 tv cell index st hin =>
    h.sweep_step hdescend hnext first level numcells tc tv1 tv index cell st hin

/-- An off-path node preserves the projected reference fields. -/
theorem node_reference (h : ReferencePolicy ctx inf tcLevel project)
    (fuel level numcells : Nat) (st : σ) :
    project (node false ctx inf tcLevel fuel level numcells st).2 = project st :=
  node_sound h.sound false fuel level numcells st rfl

/-- Later siblings preserve the projected reference fields. -/
theorem sweep_reference (h : ReferencePolicy ctx inf tcLevel project)
    (first : Bool) (fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : σ) (hpast : Past first tv1 cursor) :
    project (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 =
      project st :=
  sweep_sound h.sound first fuel cfuel level numcells tc tv1 cursor cell index st hpast

end Hex.GraphIso.Nauty.Generic
