/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.Generic

public section

namespace Hex.GraphIso.Nauty.Generic

variable {n : Nat} {σ γ : Type} [Policy σ n (γ := γ)]

/-- A persistent assertion on every node and sweep, including the first
descent, exhausted calls, and nonlocal returns. -/
def preserveContract (n : Nat) (P : σ → Prop) : Contract σ n where
  nodePre _ _ _ _ st := P st
  nodePost _ _ _ _ _ out := P out.2
  sweepPre _ _ _ _ _ _ _ _ _ _ st := P st
  sweepPost _ _ _ _ _ _ _ _ _ _ _ out := P out.2.2

/-- Local preservation rules for the actual policy operations. These have
no recursive correctness premise; `sound` composes them by the shared engine. -/
structure Preserve (ctx : γ) (inf tcLevel : Nat) (P : σ → Prop) : Prop where
  visit : ∀ level numcells st, P st → P (Policy.visit ctx level numcells st).2.2
  record : ∀ level code st, P st → P (Policy.recordFirst (n := n) level code st)
  compare : ∀ level code st, P st → P (Policy.compareCodes (n := n) level code st)
  target : ∀ first level numcells st, P st →
    P (Policy.chooseTarget first ctx tcLevel level numcells st).2.2.2
  terminal : ∀ level st, P st → P (Policy.firstterminal (n := n) level st)
  classify : ∀ level numcells st, P st → P (Policy.classify ctx level numcells st).2
  leaf : ∀ leaf level st, P st → P (Policy.leafExit (n := n) leaf level st).2
  cheap : ∀ first level st, P st → P (Policy.cheapCheck (n := n) first level st)
  child : ∀ first level tc tv st, P st → P (Policy.child (n := n) first level tc tv st)
  afterChild : ∀ level tv st, P st → P (Policy.afterChildFirst (n := n) level tv st)
  leave : ∀ tv st, P st → P (Policy.leaveChild (n := n) tv st)
  recover : ∀ level st, P st → P (Policy.recover (n := n) inf level st)
  afterSweep : ∀ first level size index st, P st →
    P (Policy.afterSweep (n := n) first level size index st)

namespace Preserve

variable {ctx : γ} {inf tcLevel : Nat} {P : σ → Prop}

theorem node_step (h : Preserve ctx inf tcLevel P) {fuel : Nat} {next : SweepFn σ n}
    (hn : (preserveContract n P).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : σ) (hp : P st) :
    P (nodeStep ctx tcLevel next first level numcells st).2 := by
  have hv := h.visit level numcells st hp
  unfold nodeStep
  generalize hr : Policy.visit ctx level numcells st = r at hv ⊢
  obtain ⟨nc, code, refined⟩ := r
  let compared := if first then Policy.recordFirst (n := n) level code refined
    else Policy.compareCodes (n := n) level code refined
  have hc : P compared := by cases first; exact h.compare _ _ _ hv; exact h.record _ _ _ hv
  have ht := h.target first level nc compared hc
  dsimp only
  generalize htr : Policy.chooseTarget first ctx tcLevel level nc compared = r at ht ⊢
  obtain ⟨tc, cell, size, targeted⟩ := r
  have hfinish : ∀ ready, P ready → P (Id.run (do
      let st := Policy.cheapCheck (n := n) first level ready
      let tv := cell.nextElem none
      let (exit, index, out) := next first level nc tc.toNat (tv.getD 0) tv cell 0 st
      match exit with
      | .done => return (Exit.unwind (level - 1) false,
          Policy.afterSweep (n := n) first level size index out)
      | _ => return (exit, out))).2 := by
    intro ready hp
    have hh := hn first level nc tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none)
      cell 0 _ (h.cheap first level ready hp)
    dsimp only
    generalize he : next first level nc tc.toNat ((cell.nextElem none).getD 0)
      (cell.nextElem none) cell 0 (Policy.cheapCheck (n := n) first level ready) = r at hh ⊢
    obtain ⟨exit, index, out⟩ := r
    cases exit
    · exact h.afterSweep first level size index out hh
    · exact hh
    · exact hh
  cases first with
  | true =>
    simp only [ite_true, Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact h.terminal level targeted ht
    · exact hfinish targeted ht
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hl := h.classify level nc targeted ht
    generalize he : Policy.classify ctx level nc targeted = r at hl ⊢
    obtain ⟨leaf, classified⟩ := r
    have hout := h.leaf leaf level classified hl
    generalize he : Policy.leafExit (n := n) leaf level classified = r at hout ⊢
    obtain ⟨exit, out⟩ := r
    cases exit
    · exact hfinish out hout
    · exact hout
    · exact hout

theorem sweep_step (h : Preserve ctx inf tcLevel P) {fuel cfuel : Nat}
    {descend : NodeFn σ} {next : SweepFn σ n}
    (hd : (preserveContract n P).nodeValid fuel descend)
    (hn : (preserveContract n P).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv index : Nat) (cell : VSet n) (st : σ) (hp : P st) :
    P (sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2 := by
  have hc := hd (first && tv == tv1) (level + 1) (numcells + 1) _
    (h.child first level tc tv st hp)
  have hcontinue : ∀ cell index out, P out →
      P (resume inf next first level numcells tc tv1 tv cell index out).2.2 := by
    intro cell index out hp
    unfold resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split <;> exact hn _ _ _ _ _ _ _ _ _ (h.recover level out hp)
  have hadvance : ∀ index out exit, P out →
      P (advance inf next first level numcells tc tv1 tv cell index out exit).2.2 := by
    intro index out exit hp
    cases exit
    · exact hcontinue _ _ _ hp
    · unfold advance
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hp
      · split <;> exact hcontinue _ _ _ hp
    · exact hp
  unfold sweepStep
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  split
  · generalize he : descend (first && tv == tv1) (level + 1) (numcells + 1)
      (Policy.child (n := n) first level tc tv st) = r at hc ⊢
    obtain ⟨exit, out⟩ := r
    split
    · exact hadvance _ _ _ (h.leave tv _ (h.afterChild level tv1 out hc))
    · exact hadvance _ _ _ (h.leave tv out hc)
  · exact hn _ _ _ _ _ _ _ _ _ hp

/-- The shared mutual recursion preserves the assertion on every path. -/
theorem sound (h : Preserve ctx inf tcLevel P) :
    SoundPolicy ctx inf tcLevel (preserveContract n P) where
  node_zero := fun _ _ _ _ hp => hp
  node_step := fun _ _ hn _ _ _ _ hp => h.node_step hn _ _ _ _ hp
  sweep_none := fun _ _ _ _ _ _ _ _ _ _ hp => hp
  sweep_zero := fun _ _ _ _ _ _ _ _ _ _ hp => hp
  sweep_step := fun _ _ _ _ hd hn _ _ _ _ _ _ _ _ _ hp => h.sweep_step hd hn _ _ _ _ _ _ _ _ _ hp

end Preserve
end Hex.GraphIso.Nauty.Generic
