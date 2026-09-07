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

variable {n : Nat} {σ : Type}

/-- A sweep is strictly past its first child, or is entirely off the first path. -/
@[expose] def Past (first : Bool) (tv1 : Nat) (cursor : Option Nat) : Prop :=
  first = true → ∀ v, cursor = some v → tv1 < v

/-- Every later bitset cursor remains past the first child. -/
theorem Past.next {first : Bool} {tv1 tv : Nat} {cell : VSet n}
    (h : first = true → tv1 < tv) : Past first tv1 (cell.nextElem (some tv)) := by
  intro hf v hv
  have hnext := (VSet.nextElem_eq_some_iff.mp hv).2.1
  change tv + 1 ≤ v at hnext
  have := h hf
  omega

/-- An invariant preserved by off-path calls and later siblings. -/
def stableContract (n : Nat) (P : σ → Prop) : Contract σ n where
  nodePre _ first _ _ st := first = false ∧ P st
  nodePost _ _ _ _ _ result := P result.2
  sweepPre _ _ first _ _ _ tv1 cursor _ _ st := Past first tv1 cursor ∧ P st
  sweepPost _ _ _ _ _ _ _ _ _ _ _ result := P result.2.2

variable [Policy σ n]

/-- Local operations outside the first descent preserve a state invariant. -/
structure StablePolicy (ctx : Ctx n) (inf tcLevel : Nat) (P : σ → Prop)
    (validCode : Nat → Prop := fun _ => True) : Prop where
  code : ∀ level numcells (st : σ), validCode (Policy.visit ctx level numcells st).2.1
  visit : ∀ level numcells st, P st → P (Policy.visit ctx level numcells st).2.2
  compare : ∀ level code st, validCode code → P st → P (Policy.compareCodes (n := n) level code st)
  target : ∀ level numcells st, P st →
    P (Policy.chooseTarget false ctx tcLevel level numcells st).2.2.2
  classify : ∀ level numcells st, P st → P (Policy.classify ctx level numcells st).2
  leaf : ∀ leaf level st, P st → P (Policy.leafExit (n := n) leaf level st).2
  cheap : ∀ first level st, P st → P (Policy.cheapCheck (n := n) first level st)
  child : ∀ first level tc tv st, P st → P (Policy.child (n := n) first level tc tv st)
  leave : ∀ tv st, P st → P (Policy.leaveChild (n := n) tv st)
  recover : ∀ level st, P st → P (Policy.recover (n := n) inf level st)
  afterSweep : ∀ first level size index st, P st →
    P (Policy.afterSweep (n := n) first level size index st)

variable {ctx : Ctx n} {inf tcLevel : Nat} {P : σ → Prop} {validCode : Nat → Prop}

/-- An off-path node preserves the state invariant. -/
theorem StablePolicy.node_step (h : StablePolicy ctx inf tcLevel P validCode)
    {fuel : Nat} {next : SweepFn σ n}
    (hnext : (stableContract n P).sweepValid fuel (n + 1) next)
    (level numcells : Nat) (st : σ) (hin : P st) :
    P (nodeStep ctx tcLevel next false level numcells st).2 := by
  have hv := h.visit level numcells st hin
  have hcode := h.code level numcells st
  unfold nodeStep
  generalize hr : Policy.visit ctx level numcells st = r at hv hcode ⊢
  obtain ⟨nc, code, refined⟩ := r
  simp only [Bool.false_eq_true, ite_false]
  let compared := Policy.compareCodes (n := n) level code refined
  have hcomp : P compared := h.compare level code refined hcode hv
  have ht := h.target level nc compared hcomp
  generalize htval : Policy.chooseTarget false ctx tcLevel level nc compared = t at ht ⊢
  obtain ⟨tc, cell, size, targeted⟩ := t
  have hcl := h.classify level nc targeted ht
  generalize hcval : Policy.classify ctx level nc targeted = c at hcl ⊢
  obtain ⟨leaf, classified⟩ := c
  have hle := h.leaf leaf level classified hcl
  generalize hlval : Policy.leafExit (n := n) leaf level classified = result at hle ⊢
  obtain ⟨exit, out⟩ := result
  have hproject : P out := hle
  cases exit with
  | fuel => exact hproject
  | unwind => exact hproject
  | done =>
    have hc := h.cheap false level out hproject
    have hn := hnext false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) false level out)
      ⟨(by intro hf; cases hf), hc⟩
    generalize hsval : next false level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) false level out) = s at hn ⊢
    obtain ⟨exit, index, result⟩ := s
    cases exit with
    | fuel => exact hn
    | unwind => exact hn
    | done => exact h.afterSweep false level size index result hn

/-- Once past the first child, all later recursive calls are off-path. -/
theorem StablePolicy.sweep_step (h : StablePolicy ctx inf tcLevel P validCode)
    {fuel cfuel : Nat} {descend : NodeFn σ} {next : SweepFn σ n}
    (hdescend : (stableContract n P).nodeValid fuel descend)
    (hnext : (stableContract n P).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : σ)
    (hpast : Past first tv1 (some tv)) (hin : P st) :
    P (sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have htv : first = true → tv1 < tv := fun hf => hpast hf tv rfl
  have hflag : (first && tv == tv1) = false := by
    cases first with
    | false => rfl
    | true =>
      have := htv rfl
      simp only [Bool.true_and, beq_eq_false_iff_ne]
      omega
  have hcontinue : ∀ cell out, P out →
      P (next first level numcells tc tv1 (cell.nextElem (some tv)) cell
        (if first && Policy.orbit (n := n) (Policy.recover (n := n) inf level out) tv == tv1
          then index + 1 else index)
        (Policy.recover (n := n) inf level out)).2.2 := by
    intro cell out heq
    exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ _
      ⟨Past.next htv, h.recover level out heq⟩
  have hd := hdescend false (level + 1) (numcells + 1)
    (Policy.child (n := n) first level tc tv st) ⟨rfl, h.child first level tc tv st hin⟩
  unfold sweepStep
  simp only [hflag, Bool.false_eq_true, ite_false, Id.run_pure,
    apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize hdval : descend false (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = result at hd ⊢
    obtain ⟨exit, out⟩ := result
    have heq := h.leave tv out hd
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
  · exact hnext first level numcells tc tv1 (cell.nextElem (some tv)) cell _ st ⟨Past.next htv, hin⟩

/-- Local preservation gives the generic invariant contract. -/
theorem StablePolicy.sound (h : StablePolicy ctx inf tcLevel P validCode) :
    SoundPolicy ctx inf tcLevel (stableContract n P) where
  node_zero := fun _ _ _ _ hin => hin.2
  node_step := by
    intro fuel next hnext first level numcells st hin
    obtain ⟨rfl, hin⟩ := hin
    exact h.node_step hnext level numcells st hin
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ hin => hin.2
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ hin => hin.2
  sweep_step := fun _ _ _ _ hdescend hnext first level numcells tc tv1 tv cell index st hin =>
    h.sweep_step hdescend hnext first level numcells tc tv1 tv index cell st hin.1 hin.2

/-- An off-path node preserves an invariant stable under its local operations. -/
theorem node_stable (h : StablePolicy ctx inf tcLevel P validCode)
    (fuel level numcells : Nat) (st : σ) (hin : P st) :
    P (node false ctx inf tcLevel fuel level numcells st).2 :=
  node_sound h.sound false fuel level numcells st ⟨rfl, hin⟩

/-- A later sibling sweep preserves the same invariant. -/
theorem sweep_stable (h : StablePolicy ctx inf tcLevel P validCode)
    (first : Bool) (fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : σ)
    (hpast : Past first tv1 cursor) (hin : P st) :
    P (sweep first ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2 :=
  sweep_sound h.sound first fuel cfuel level numcells tc tv1 cursor cell index st ⟨hpast, hin⟩

end Hex.GraphIso.Nauty.Generic
